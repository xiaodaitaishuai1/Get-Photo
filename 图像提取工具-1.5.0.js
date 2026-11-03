// ==UserScript==
// @name         图像提取工具
// @namespace    http://tampermonkey.net/
// @version      1.5.0
// @description  提取当前页面大图（默认 >=500px，可在面板中调整），兼容 Chrome/Tampermonkey，支持横向优先瀑布流、尺寸记忆跳过、批量反选、菜单式面板、小红书链接解析、半隐式边缘吸附入口、日志查看、发布日期命名与稳定串行下载。
// @author       guliacer
// @homepageURL  https://github.com/guliacer/GetPhoto
// @supportURL   https://github.com/guliacer/GetPhoto/issues
// @match        *://*/*
// @run-at       document-idle
// @noframes
// @grant        GM_addStyle
// @grant        GM_download
// @grant        GM_registerMenuCommand
// @grant        GM_notification
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_setClipboard
// @connect      *
// ==/UserScript==

(function () {
    'use strict';

    if (window.__TM_IMAGE_EXTRACTOR_READY__) {
        return;
    }
    window.__TM_IMAGE_EXTRACTOR_READY__ = true;

    const VERSION = '1.5.0';
    const ROOT_ID = 'tmImageExtractor';
    const DEFAULT_MIN_SIZE = 500;
    const DEFAULT_DOWNLOAD_DELAY = 800;
    const MIN_SIZE_LIMITS = { min: 100, max: 8000 };
    const DOWNLOAD_DELAY_LIMITS = { min: 0, max: 10000 };
    const PROBE_TIMEOUT = 10000;
    const PROBE_CONCURRENCY = 6;
    const MAX_FOLDER_LENGTH = 70;
    const MAX_FILE_LENGTH = 120;
    const MAX_TITLE_UNITS = 20;
    const MAX_LOG_ENTRIES = 600;
    const FLOATING_BUTTON_MARGIN = 20;
    const FLOATING_DOCK_OFFSET = -18;
    const FLOATING_REVEAL_SHIFT = Math.abs(FLOATING_DOCK_OFFSET);
    const FLOATING_BUTTON_BOTTOM = 140;
    const FLOATING_DRAG_THRESHOLD = 5;
    const STORAGE_KEYS = {
        loggingEnabled: 'tmie.loggingEnabled',
        pluginEnabled: 'tmie.pluginEnabled',
        floatingPosition: 'tmie.floatingPosition',
        minSize: 'tmie.minSize',
        sizeCache: 'tmie.sizeCache',
        downloadDelay: 'tmie.downloadDelay',
        hiddenSizes: 'tmie.hiddenSizes'
    };
    const RESERVED_WINDOWS_NAMES = /^(con|prn|aux|nul|com[1-9]|lpt[1-9])$/i;
    // 只放确定表示尺寸/画质的参数。'q' 和 'size' 已剔除：
    // 前者常是搜索词(render?q=cat)，后者常是变体名(i?size=avatarA)，删了会把不同图误判成同一张。
    const SIZE_QUERY_PARAMS = [
        'w', 'h', 'width', 'height', 'thumb', 'thumbnail',
        'quality', 'resize', 'scale', 'dpr', 'imageView2', 'x-oss-process'
    ];
    const UI_MARK_ATTR = 'data-tmie-ui';
    const SIZE_CACHE_LIMIT = 1500;
    const BACKGROUND_SCAN_SELECTOR = 'div, span, a, li, section, figure, i';
    const BACKGROUND_SCAN_LIMIT = 3000;
    const BACKGROUND_MIN_BOX = 200;
    const DEFAULT_HIDDEN_SIZES = new Set([
        '1500x1500',
        '1500x1000',
        '1000x1500',
        '1000x750',
        '1280x720',
        '853x1280',
        '1280x853',
        '1001x1500',
        '1500x1001'
    ]);
    const SITE_NAME_MAP = new Map([
        ['zcool.com.cn', '站酷'],
        ['www.zcool.com.cn', '站酷'],
        ['xiaohongshu.com', '小红书'],
        ['www.xiaohongshu.com', '小红书']
    ]);
    const MORANDI_PALETTES = [
        { accent: '#c38f85', accentSoft: '#e7d6d0', accentStrong: '#a87066', surface: '#f7f1ec', surfaceMuted: '#efe5de' },
        { accent: '#8aa1a8', accentSoft: '#dde7e9', accentStrong: '#708890', surface: '#f5f7f7', surfaceMuted: '#e7eeef' },
        { accent: '#9f9b87', accentSoft: '#e6e2d5', accentStrong: '#837f69', surface: '#f7f5ef', surfaceMuted: '#eeebde' },
        { accent: '#a98b97', accentSoft: '#eadce2', accentStrong: '#8f727e', surface: '#f8f3f5', surfaceMuted: '#f0e7ea' }
    ];
    const AD_CONTEXT_PATTERNS = [
        /(^|\.)doubleclick\.net$/i,
        /(^|\.)googlesyndication\.com$/i,
        /(^|\.)googleadservices\.com$/i,
        /(^|\.)adservice\.google\./i,
        /(^|\.)pos\.baidu\.com$/i,
        /(^|\.)cpro\.baidu\.com$/i,
        /(^|\.)alimama\.com$/i,
        /(^|\.)tanx\.com$/i,
        /(^|\.)adsystem\.com$/i,
        /(^|\.)adnxs\.com$/i
    ];
    const XHS_LINK_HELPER = {
        markAttr: 'data-tmie-xhs-link-processed',
        styleId: `${ROOT_ID}XhsLinkStyle`,
        linkClass: `${ROOT_ID}XhsLinkAnchor`,
        targetSelectors: [
            '#detail-desc',
            '#detail-desc > .note-text > span',
            '.note-content .desc',
            '.note-container .content',
            '.comment-content',
            '.comments-container .content',
            '[class*="comment"] [class*="content"]'
        ],
        guidePatterns: [
            /薯队长发布了一篇小红书笔记，快来看吧！/gi,
            /😆.*?😆/gi,
            /，复制本条信息，打开【小红书】App查看精彩内容！/gi,
            /复制这段内容后打开百度网盘手机App，操作更方便哦/gi,
            /【淘宝】/gi,
            /点击链接直接打开\s*或者\s*淘宝搜索直接打开/gi,
            /复制.*?打开.*?App/gi,
            /链接:\s*/gi
        ],
        urlRegex: /((?:https?|ftp|file):\/\/[^\s<>"'`]+)/gi,
        skipTags: new Set(['A', 'BUTTON', 'SCRIPT', 'STYLE', 'NOSCRIPT', 'TEXTAREA'])
    };

    if (shouldSkipExecutionContext()) {
        return;
    }

    const palette = MORANDI_PALETTES[Math.floor(Math.random() * MORANDI_PALETTES.length)];
    const state = {
        allImages: [],
        filteredImages: [],
        imageOrder: new Map(),
        suppressedSizeCounts: new Map(),
        sizeCache: readStoredSizeCache(),
        selectedImages: new Set(),
        suppressedSizes: readStoredHiddenSizes(),
        minSize: readStoredNumber(STORAGE_KEYS.minSize, DEFAULT_MIN_SIZE, MIN_SIZE_LIMITS),
        downloadDelay: readStoredNumber(STORAGE_KEYS.downloadDelay, DEFAULT_DOWNLOAD_DELAY, DOWNLOAD_DELAY_LIMITS),
        pluginEnabled: readStoredBoolean(STORAGE_KEYS.pluginEnabled, true),
        floatingButtonPosition: readStoredFloatingPosition(),
        isDownloading: false,
        showLogViewer: false,
        loggingEnabled: readStoredBoolean(STORAGE_KEYS.loggingEnabled, false),
        logs: [],
        pageMeta: null
    };

    function shouldSkipExecutionContext() {
        if (isEmbeddedFrame()) {
            return true;
        }

        const host = window.location.hostname || '';
        if (AD_CONTEXT_PATTERNS.some((pattern) => pattern.test(host))) {
            return true;
        }

        const isPopupWindow = Boolean(window.opener);
        const isSmallViewport = window.innerWidth <= 640 || window.innerHeight <= 520;
        const adUrlHint = /(?:^|[./?&_-])(ad|ads|advert|advertise|adserver|banner|cpro|promo|sponsor)(?:[./?&=_-]|$)/i.test(window.location.href);
        return isPopupWindow && (isSmallViewport || adUrlHint);
    }

    function isEmbeddedFrame() {
        try {
            return window.self !== window.top;
        } catch {
            return true;
        }
    }

    const BASE_CSS = `
        :root {
            --tmie-accent: ${palette.accent};
            --tmie-accent-soft: ${palette.accentSoft};
            --tmie-accent-strong: ${palette.accentStrong};
            --tmie-surface: ${palette.surface};
            --tmie-surface-muted: ${palette.surfaceMuted};
            --tmie-text: #514944;
            --tmie-text-soft: #756c67;
            --tmie-border: rgba(89, 72, 64, 0.14);
            --tmie-shadow: 0 18px 42px rgba(45, 34, 29, 0.16);
            --tmie-shadow-soft: 0 8px 22px rgba(45, 34, 29, 0.1);
            --tmie-danger: #b86868;
            --tmie-success: #709a79;
            --tmie-warning: #c29a56;
        }

        #${ROOT_ID}FloatingButton {
            position: fixed;
            right: ${FLOATING_DOCK_OFFSET}px;
            bottom: ${FLOATING_BUTTON_BOTTOM}px;
            display: inline-flex;
            align-items: center;
            justify-content: center;
            width: 56px;
            height: 56px;
            border: 1px solid rgba(255, 255, 255, 0.72);
            border-radius: 50%;
            background:
                radial-gradient(circle at 32% 24%, rgba(255, 255, 255, 0.98), rgba(255, 255, 255, 0.48) 36%, transparent 37%),
                linear-gradient(145deg, var(--tmie-accent), var(--tmie-accent-strong));
            color: #fff;
            box-shadow:
                0 16px 34px rgba(45, 34, 29, 0.2),
                0 4px 12px rgba(45, 34, 29, 0.12),
                inset 0 1px 0 rgba(255, 255, 255, 0.5);
            cursor: pointer;
            z-index: 2147483645;
            opacity: 0.38;
            touch-action: none;
            user-select: none;
            transition:
                transform 0.2s ease,
                box-shadow 0.2s ease,
                opacity 0.2s ease,
                filter 0.2s ease;
            overflow: visible;
        }

        #${ROOT_ID}FloatingButton::before {
            content: "";
            position: absolute;
            inset: 7px;
            border-radius: inherit;
            border: 1px solid rgba(255, 255, 255, 0.34);
            pointer-events: none;
        }

        #${ROOT_ID}FloatingButton::after {
            content: "提取图片";
            position: absolute;
            top: 50%;
            right: calc(100% + 10px);
            transform: translate(6px, -50%);
            max-width: 96px;
            padding: 7px 10px;
            border-radius: 999px;
            background: rgba(43, 34, 31, 0.9);
            color: #fff;
            box-shadow: 0 10px 22px rgba(45, 34, 29, 0.18);
            font-size: 12px;
            font-weight: 650;
            line-height: 1;
            white-space: nowrap;
            opacity: 0;
            pointer-events: none;
            transition: transform 0.18s ease, opacity 0.18s ease;
        }

        #${ROOT_ID}FloatingButton[data-edge="left"]::after {
            right: auto;
            left: calc(100% + 10px);
            transform: translate(-6px, -50%);
        }

        .${ROOT_ID}FloatingIcon {
            position: relative;
            width: 27px;
            height: 27px;
            filter: drop-shadow(0 2px 4px rgba(45, 34, 29, 0.22));
        }

        .${ROOT_ID}FloatingIcon svg {
            display: block;
            width: 100%;
            height: 100%;
        }

        #${ROOT_ID}FloatingButton:hover {
            transform: translateY(-2px) translateX(-${FLOATING_REVEAL_SHIFT}px) scale(1.04);
            opacity: 0.96;
            filter: saturate(1.08);
            box-shadow:
                0 20px 42px rgba(45, 34, 29, 0.24),
                0 8px 18px rgba(45, 34, 29, 0.14),
                inset 0 1px 0 rgba(255, 255, 255, 0.56);
        }

        #${ROOT_ID}FloatingButton[data-edge="left"]:hover {
            transform: translateY(-2px) translateX(${FLOATING_REVEAL_SHIFT}px) scale(1.04);
        }

        #${ROOT_ID}FloatingButton:hover::after,
        #${ROOT_ID}FloatingButton:focus-visible::after {
            opacity: 1;
            transform: translate(0, -50%);
        }

        #${ROOT_ID}FloatingButton[data-edge="left"]:hover::after,
        #${ROOT_ID}FloatingButton[data-edge="left"]:focus-visible::after {
            transform: translate(0, -50%);
        }

        #${ROOT_ID}FloatingButton:focus-visible {
            outline: none;
            opacity: 0.96;
            transform: translateX(-${FLOATING_REVEAL_SHIFT}px);
            box-shadow:
                0 0 0 4px rgba(195, 143, 133, 0.22),
                0 20px 42px rgba(45, 34, 29, 0.24),
                inset 0 1px 0 rgba(255, 255, 255, 0.56);
        }

        #${ROOT_ID}FloatingButton[data-edge="left"]:focus-visible {
            transform: translateX(${FLOATING_REVEAL_SHIFT}px);
        }

        #${ROOT_ID}FloatingButton:active {
            opacity: 1;
            transform: translateY(0) translateX(-${FLOATING_REVEAL_SHIFT}px) scale(0.98);
        }

        #${ROOT_ID}FloatingButton[data-edge="left"]:active {
            transform: translateY(0) translateX(${FLOATING_REVEAL_SHIFT}px) scale(0.98);
        }

        #${ROOT_ID}FloatingButton.dragging {
            cursor: grabbing;
            transform: scale(1.06);
            transition: none;
            opacity: 0.92;
        }

        #${ROOT_ID}FloatingButton.dragging::after {
            opacity: 0;
        }

        @media (max-width: 560px) {
            #${ROOT_ID}FloatingButton {
                width: 50px;
                height: 50px;
            }

            .${ROOT_ID}FloatingIcon {
                width: 24px;
                height: 24px;
            }

            #${ROOT_ID}FloatingButton::after {
                display: none;
            }
        }
    `;

    const PANEL_CSS = `
        #${ROOT_ID}Modal,
        #${ROOT_ID}LogModal {
            position: fixed;
            inset: 0;
            z-index: 2147483646;
            display: flex;
            flex-direction: column;
            gap: 16px;
            padding: 18px;
            overflow: auto;
            box-sizing: border-box;
            backdrop-filter: blur(6px);
            background:
                radial-gradient(circle at top left, rgba(255,255,255,0.22), transparent 34%),
                linear-gradient(180deg, rgba(44, 35, 31, 0.72), rgba(28, 23, 21, 0.82));
        }

        #${ROOT_ID}Panel,
        #${ROOT_ID}LogPanel {
            max-width: 1560px;
            width: 100%;
            margin: 0 auto;
            border-radius: 22px;
            background:
                linear-gradient(180deg, rgba(255,255,255,0.9), rgba(255,255,255,0.82)),
                linear-gradient(135deg, var(--tmie-surface), var(--tmie-surface-muted));
            box-shadow: var(--tmie-shadow);
            border: 1px solid rgba(255,255,255,0.38);
        }

        #${ROOT_ID}Panel {
            position: sticky;
            top: 0;
            z-index: 5;
            padding: 18px;
        }

        #${ROOT_ID}Header,
        #${ROOT_ID}LogHeader {
            display: flex;
            align-items: flex-start;
            justify-content: space-between;
            gap: 16px;
            margin-bottom: 16px;
        }

        #${ROOT_ID}Header h2,
        #${ROOT_ID}LogHeader h2 {
            margin: 0;
            color: var(--tmie-text);
            font-size: 22px;
            line-height: 1.35;
        }

        #${ROOT_ID}Header p,
        #${ROOT_ID}LogHeader p {
            margin: 6px 0 0;
            color: var(--tmie-text-soft);
            font-size: 13px;
            line-height: 1.6;
        }

        .${ROOT_ID}Btn {
            border: 0;
            border-radius: 999px;
            padding: 9px 16px;
            background: #ffffff;
            color: var(--tmie-text);
            cursor: pointer;
            box-shadow: inset 0 0 0 1px var(--tmie-border);
            transition: transform 0.15s ease, background 0.15s ease, color 0.15s ease;
            font-size: 13px;
            font-weight: 600;
        }

        .${ROOT_ID}Btn:hover:not(:disabled) {
            transform: translateY(-1px);
            background: var(--tmie-accent-soft);
        }

        .${ROOT_ID}Btn:disabled {
            opacity: 0.58;
            cursor: not-allowed;
        }

        .${ROOT_ID}Btn.primary {
            background: var(--tmie-accent);
            color: #fff;
            box-shadow: none;
        }

        .${ROOT_ID}Btn.primary:hover:not(:disabled) {
            background: var(--tmie-accent-strong);
        }

        .${ROOT_ID}Btn.success {
            background: var(--tmie-success);
            color: #fff;
            box-shadow: none;
        }

        .${ROOT_ID}Btn.warn {
            background: var(--tmie-warning);
            color: #fff;
            box-shadow: none;
        }

        #${ROOT_ID}Toolbar,
        #${ROOT_ID}LogToolbar {
            display: flex;
            flex-wrap: wrap;
            gap: 10px;
            align-items: center;
        }

        #${ROOT_ID}Stats {
            display: flex;
            flex-wrap: wrap;
            gap: 10px;
            margin-left: auto;
        }

        .${ROOT_ID}PopWrap {
            position: relative;
            display: inline-flex;
        }

        /* 主操作 + 右侧下拉箭头，视觉上拼成一个控件 */
        .${ROOT_ID}Split {
            display: inline-flex;
            align-items: stretch;
            gap: 1px;
        }

        .${ROOT_ID}Split > .${ROOT_ID}Btn:first-child {
            border-radius: 999px 0 0 999px;
            padding-right: 13px;
        }

        .${ROOT_ID}Split > .${ROOT_ID}PopWrap > .${ROOT_ID}Caret {
            border-radius: 0 999px 999px 0;
            padding: 9px 11px;
            font-size: 11px;
            height: 100%;
        }

        /* 最小尺寸：标签 + 输入框 + 箭头，外面套一圈边框当成整体 */
        .${ROOT_ID}Field {
            display: inline-flex;
            align-items: center;
            gap: 8px;
            padding: 0 4px 0 12px;
            border-radius: 999px;
            background: #fff;
            box-shadow: inset 0 0 0 1px var(--tmie-border);
        }

        .${ROOT_ID}Field > label {
            color: var(--tmie-text-soft);
            font-size: 12px;
            font-weight: 600;
            white-space: nowrap;
        }

        .${ROOT_ID}Field #${ROOT_ID}MinSize {
            width: 68px;
            border: 0;
            box-shadow: none;
            background: transparent;
            padding: 8px 0;
            font-weight: 600;
        }

        .${ROOT_ID}Field .${ROOT_ID}Caret {
            padding: 7px 10px;
            font-size: 11px;
            box-shadow: none;
            background: transparent;
            color: var(--tmie-text-soft);
        }

        .${ROOT_ID}Field .${ROOT_ID}Caret:hover:not(:disabled) {
            background: var(--tmie-accent-soft);
            color: var(--tmie-text);
        }

        /* 尺寸筛选弹层要放一排尺寸按钮，比其它菜单宽一些 */
        .${ROOT_ID}Pop.wide {
            min-width: 320px;
            max-width: 460px;
        }

        .${ROOT_ID}Pop {
            position: absolute;
            top: calc(100% + 8px);
            left: 0;
            z-index: 30;
            min-width: 268px;
            max-width: 380px;
            padding: 14px;
            border-radius: 16px;
            background: linear-gradient(180deg, #ffffff, var(--tmie-surface));
            box-shadow: var(--tmie-shadow);
            border: 1px solid var(--tmie-border);
            display: flex;
            flex-direction: column;
            gap: 10px;
        }

        .${ROOT_ID}Pop[hidden] {
            display: none !important;
        }

        .${ROOT_ID}Pop.alignRight {
            left: auto;
            right: 0;
        }

        .${ROOT_ID}PopRow {
            display: flex;
            align-items: center;
            justify-content: space-between;
            gap: 10px;
        }

        .${ROOT_ID}PopRow > label {
            color: var(--tmie-text);
            font-size: 13px;
            font-weight: 600;
        }

        .${ROOT_ID}PopHint {
            margin: 0;
            color: var(--tmie-text-soft);
            font-size: 12px;
            line-height: 1.6;
        }

        .${ROOT_ID}PopDivider {
            height: 1px;
            background: var(--tmie-border);
        }

        .${ROOT_ID}Btn.ghost {
            background: transparent;
            color: var(--tmie-text-soft);
        }

        .${ROOT_ID}Btn[aria-expanded="true"] {
            background: var(--tmie-accent-soft);
            color: var(--tmie-text);
        }

        .${ROOT_ID}PopList {
            display: flex;
            flex-direction: column;
            gap: 8px;
        }

        .${ROOT_ID}PopList .${ROOT_ID}Chip {
            text-align: left;
            line-height: 1.5;
        }

        .${ROOT_ID}Chip {
            padding: 7px 12px;
            border-radius: 999px;
            background: rgba(255,255,255,0.84);
            box-shadow: inset 0 0 0 1px var(--tmie-border);
            color: var(--tmie-text-soft);
            font-size: 12px;
            font-weight: 600;
        }

        .${ROOT_ID}Chip.warn {
            color: var(--tmie-warning);
        }

        .${ROOT_ID}Chip.success {
            color: var(--tmie-success);
        }

        .${ROOT_ID}Chip.accent {
            background: var(--tmie-accent);
            color: #fff;
            box-shadow: none;
        }

        #${ROOT_ID}StartIndex,
        #${ROOT_ID}MinSize,
        #${ROOT_ID}DownloadDelay {
            width: 96px;
            padding: 8px 12px;
            border-radius: 999px;
            border: 1px solid var(--tmie-border);
            outline: none;
            background: #fff;
            color: var(--tmie-text);
            font-size: 13px;
            text-align: center;
        }

        #${ROOT_ID}FilterButtons {
            display: flex;
            flex-wrap: wrap;
            gap: 8px;
            max-height: 216px;
            overflow-y: auto;
        }

        #${ROOT_ID}FilterButtons:empty::after {
            content: "当前没有可筛选的尺寸";
            color: var(--tmie-text-soft);
            font-size: 12px;
        }

        .${ROOT_ID}FilterBtn {
            border: 0;
            border-radius: 999px;
            padding: 8px 12px;
            cursor: pointer;
            background: rgba(255,255,255,0.88);
            color: var(--tmie-text);
            box-shadow: inset 0 0 0 1px var(--tmie-border);
            font-size: 12px;
            font-weight: 600;
            transition: transform 0.15s ease, background 0.15s ease;
        }

        .${ROOT_ID}FilterBtn:hover {
            transform: translateY(-1px);
        }

        .${ROOT_ID}FilterBtn.suppressed {
            background: rgba(117, 108, 103, 0.08);
            color: var(--tmie-text-soft);
        }

        .${ROOT_ID}FilterBtn.visible {
            background: var(--tmie-accent);
            color: #fff;
            box-shadow: none;
        }

        #${ROOT_ID}Gallery {
            max-width: 1560px;
            width: 100%;
            margin: 0 auto;
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(250px, 1fr));
            grid-auto-rows: 8px;
            gap: 16px;
            align-items: start;
        }

        .${ROOT_ID}Card {
            display: block;
            width: 100%;
            margin: 0;
            border-radius: 18px;
            overflow: hidden;
            background: linear-gradient(180deg, rgba(255,255,255,0.98), rgba(246,241,236,0.98));
            box-shadow: var(--tmie-shadow-soft);
            border: 1px solid rgba(255,255,255,0.42);
            transition: transform 0.18s ease, box-shadow 0.18s ease, outline-color 0.18s ease;
            outline: 2px solid transparent;
            cursor: pointer;
        }

        .${ROOT_ID}Card[hidden],
        .${ROOT_ID}Empty[hidden] {
            display: none !important;
        }

        .${ROOT_ID}Card:focus-visible {
            outline-color: var(--tmie-accent-strong);
            outline-offset: 2px;
        }

        .${ROOT_ID}Card:hover {
            transform: translateY(-2px);
            box-shadow: 0 14px 28px rgba(45, 34, 29, 0.16);
        }

        .${ROOT_ID}Card.selected {
            outline-color: var(--tmie-accent);
            transform: translateY(-3px);
            box-shadow: 0 18px 36px rgba(195, 143, 133, 0.28);
        }

        .${ROOT_ID}ThumbWrap {
            position: relative;
            overflow: hidden;
            aspect-ratio: var(--tmie-image-ratio, auto);
            background: #ece4de;
        }

        .${ROOT_ID}Thumb {
            display: block;
            width: 100%;
            height: 100%;
            object-fit: cover;
            background: #ece4de;
            cursor: zoom-in;
            transition: transform 0.24s ease, filter 0.24s ease;
        }

        .${ROOT_ID}Card:hover .${ROOT_ID}Thumb {
            transform: scale(1.015);
        }

        .${ROOT_ID}Card.selected .${ROOT_ID}Thumb {
            transform: scale(1.01);
            filter: brightness(0.86) saturate(0.96);
        }

        .${ROOT_ID}CardBody {
            padding: 12px 13px 14px;
            display: flex;
            align-items: center;
            justify-content: space-between;
            gap: 12px;
        }

        .${ROOT_ID}Meta {
            margin: 0;
            color: var(--tmie-text-soft);
            font-size: 12px;
            line-height: 1.5;
            word-break: break-all;
        }

        .${ROOT_ID}SelectState {
            flex: 0 0 auto;
            display: inline-flex;
            align-items: center;
            gap: 8px;
            padding: 8px 12px;
            border-radius: 999px;
            background: rgba(255,255,255,0.82);
            color: var(--tmie-text-soft);
            box-shadow: inset 0 0 0 1px var(--tmie-border);
            transition: background 0.2s ease, color 0.2s ease, transform 0.2s ease, box-shadow 0.2s ease;
            font-size: 12px;
            font-weight: 700;
        }

        .${ROOT_ID}Card.selected .${ROOT_ID}SelectState {
            background: linear-gradient(160deg, rgba(195, 143, 133, 0.98), rgba(168, 130, 122, 0.98));
            color: #fff;
            box-shadow: 0 10px 20px rgba(156, 107, 97, 0.2);
            transform: translateY(-1px);
        }

        .${ROOT_ID}SelectStateIcon {
            width: 22px;
            height: 22px;
            border-radius: 50%;
            display: inline-flex;
            align-items: center;
            justify-content: center;
            font-size: 13px;
            font-weight: 800;
            background: rgba(255,255,255,0.8);
            color: var(--tmie-accent-strong);
        }

        .${ROOT_ID}Card.selected .${ROOT_ID}SelectStateIcon {
            background: rgba(255,255,255,0.18);
            color: #fff;
        }

        .${ROOT_ID}Label {
            display: flex;
            align-items: center;
            gap: 8px;
            color: var(--tmie-text);
            font-size: 13px;
            font-weight: 600;
            cursor: pointer;
            user-select: none;
        }

        .${ROOT_ID}Label input {
            width: 16px;
            height: 16px;
            accent-color: var(--tmie-accent);
            cursor: pointer;
        }

        .${ROOT_ID}Empty {
            grid-column: 1 / -1;
            max-width: 460px;
            margin: 64px auto;
            padding: 24px;
            border-radius: 20px;
            background: rgba(255,255,255,0.86);
            color: var(--tmie-text);
            text-align: center;
            box-shadow: var(--tmie-shadow);
        }

        #${ROOT_ID}Loading {
            position: fixed;
            left: 50%;
            top: 30px;
            transform: translateX(-50%);
            z-index: 2147483647;
            padding: 10px 16px;
            border-radius: 999px;
            background: rgba(33, 27, 24, 0.86);
            color: #fff;
            font-size: 13px;
            box-shadow: var(--tmie-shadow-soft);
        }

        #${ROOT_ID}LogPanel {
            padding: 18px;
            max-width: 1280px;
        }

        #${ROOT_ID}LogList {
            max-height: 68vh;
            overflow: auto;
            padding: 12px;
            border-radius: 18px;
            background: rgba(255,255,255,0.65);
            box-shadow: inset 0 0 0 1px var(--tmie-border);
            font-family: Consolas, "Courier New", monospace;
            font-size: 12px;
            line-height: 1.65;
            color: var(--tmie-text);
            white-space: pre-wrap;
            word-break: break-word;
        }

        .${ROOT_ID}LogLine {
            padding: 8px 10px;
            border-radius: 12px;
            margin-bottom: 8px;
            background: rgba(255,255,255,0.72);
        }

        .${ROOT_ID}LogLine.error {
            background: rgba(184, 104, 104, 0.12);
        }

        .${ROOT_ID}LogLine.warn {
            background: rgba(194, 154, 86, 0.12);
        }

        .${ROOT_ID}LogLine.debug {
            background: rgba(112, 154, 121, 0.1);
        }

        @media (max-width: 900px) {
            #${ROOT_ID}Modal,
            #${ROOT_ID}LogModal {
                padding: 12px;
            }

            #${ROOT_ID}Panel,
            #${ROOT_ID}LogPanel {
                padding: 14px;
                border-radius: 18px;
            }

            #${ROOT_ID}Gallery {
                grid-template-columns: repeat(auto-fill, minmax(220px, 1fr));
                gap: 14px;
            }
        }

        @media (max-width: 560px) {
            #${ROOT_ID}Header,
            #${ROOT_ID}LogHeader {
                flex-direction: column;
            }

            #${ROOT_ID}Toolbar,
            #${ROOT_ID}LogToolbar {
                align-items: stretch;
            }

            #${ROOT_ID}Stats {
                width: 100%;
                margin-left: 0;
            }

            #${ROOT_ID}Gallery {
                grid-template-columns: 1fr;
                gap: 14px;
            }

            .${ROOT_ID}CardBody {
                align-items: flex-start;
                flex-direction: column;
            }
        }
    `;

    let panelCssInjected = false;

    function injectPanelCss() {
        if (panelCssInjected) {
            return;
        }
        panelCssInjected = true;
        GM_addStyle(PANEL_CSS);
    }

    GM_addStyle(BASE_CSS);

    function readStoredBoolean(key, fallback) {
        try {
            return Boolean(GM_getValue(key, fallback));
        } catch {
            return fallback;
        }
    }

    function storeBoolean(key, value) {
        try {
            GM_setValue(key, Boolean(value));
        } catch (error) {
            console.warn('[图像提取工具] 保存设置失败:', error);
        }
    }

    function readStoredValue(key, fallback) {
        try {
            return GM_getValue(key, fallback);
        } catch {
            return fallback;
        }
    }

    function storeValue(key, value) {
        try {
            GM_setValue(key, value);
        } catch (error) {
            console.warn('[图像提取工具] 保存设置失败:', error);
        }
    }

    function readStoredNumber(key, fallback, limits) {
        const value = Number(readStoredValue(key, fallback));
        if (!Number.isFinite(value)) {
            return fallback;
        }
        return clampNumber(Math.round(value), limits.min, limits.max);
    }

    // 记住每个图片指纹的真实尺寸，下次访问同一页面时若该尺寸已被记忆隐藏，
    // 可以直接跳过探测请求。只用于「跳过」判断，不用于放宽 minSize 判断。
    function readStoredSizeCache() {
        const stored = readStoredValue(STORAGE_KEYS.sizeCache, null);
        if (!stored || typeof stored !== 'object') {
            return new Map();
        }
        const entries = Object.entries(stored)
            .filter(([, value]) => typeof value === 'string' && /^\d+x\d+$/.test(value));
        return new Map(entries);
    }

    function persistSizeCache() {
        const cache = state.sizeCache;
        // 超出上限时丢掉最早写入的条目（Map 保持插入顺序）
        if (cache.size > SIZE_CACHE_LIMIT) {
            const excess = cache.size - SIZE_CACHE_LIMIT;
            let dropped = 0;
            for (const key of cache.keys()) {
                cache.delete(key);
                dropped += 1;
                if (dropped >= excess) {
                    break;
                }
            }
        }
        storeValue(STORAGE_KEYS.sizeCache, Object.fromEntries(cache));
    }

    function readStoredHiddenSizes() {
        const stored = readStoredValue(STORAGE_KEYS.hiddenSizes, null);
        if (!Array.isArray(stored)) {
            return new Set(DEFAULT_HIDDEN_SIZES);
        }
        return new Set(stored.filter((item) => typeof item === 'string' && /^\d+x\d+$/.test(item)));
    }

    function readStoredFloatingPosition() {
        const value = readStoredValue(STORAGE_KEYS.floatingPosition, null);
        const edge = value?.edge === 'left' ? 'left' : 'right';
        const y = Number(value?.y);
        return {
            edge,
            y: Number.isFinite(y) ? y : null
        };
    }

    function getNowTime() {
        const now = new Date();
        const hh = String(now.getHours()).padStart(2, '0');
        const mm = String(now.getMinutes()).padStart(2, '0');
        const ss = String(now.getSeconds()).padStart(2, '0');
        return `${hh}:${mm}:${ss}`;
    }

    function escapeHtml(value) {
        return String(value ?? '')
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&#39;');
    }

    function sleep(ms) {
        return new Promise((resolve) => window.setTimeout(resolve, ms));
    }

    async function mapWithConcurrency(items, limit, worker) {
        const size = items.length;
        if (size === 0) {
            return;
        }

        let cursor = 0;
        const runners = Array.from({ length: Math.min(limit, size) }, async () => {
            while (cursor < size) {
                const index = cursor;
                cursor += 1;
                await worker(items[index], index);
            }
        });

        await Promise.all(runners);
    }

    function notify(message, title = '图像提取工具') {
        if (typeof GM_notification === 'function') {
            GM_notification({ title, text: message, timeout: 3500 });
            return;
        }
        window.alert(message);
    }

    function showLoading(message) {
        injectPanelCss();
        hideLoading();
        const node = document.createElement('div');
        node.id = `${ROOT_ID}Loading`;
        node.setAttribute(UI_MARK_ATTR, '1');
        node.textContent = message;
        document.body.appendChild(node);
    }

    function hideLoading() {
        document.getElementById(`${ROOT_ID}Loading`)?.remove();
    }

    function addLog(level, message, details) {
        const logLevel = String(level || 'info').toLowerCase();
        const consoleMethod = logLevel === 'error' ? 'error' : logLevel === 'warn' ? 'warn' : 'log';
        console[consoleMethod](`[图像提取工具][${logLevel}] ${message}`, details || '');

        if (!state.loggingEnabled && !['warn', 'error'].includes(logLevel)) {
            return;
        }

        const entry = {
            time: getNowTime(),
            level: logLevel,
            message,
            details: details ?? null
        };
        state.logs.push(entry);
        if (state.logs.length > MAX_LOG_ENTRIES) {
            state.logs.splice(0, state.logs.length - MAX_LOG_ENTRIES);
        }
        refreshLogViewer();
    }

    function formatLogEntry(entry) {
        const detailText = entry.details ? `\n${JSON.stringify(entry.details, null, 2)}` : '';
        return `[${entry.time}] [${entry.level.toUpperCase()}] ${entry.message}${detailText}`;
    }

    function getLogsAsText() {
        return state.logs.map(formatLogEntry).join('\n\n');
    }

    async function copyLogsToClipboard() {
        const text = getLogsAsText() || '暂无日志。';
        try {
            if (typeof GM_setClipboard === 'function') {
                GM_setClipboard(text, 'text');
            } else if (navigator.clipboard?.writeText) {
                await navigator.clipboard.writeText(text);
            } else {
                throw new Error('clipboard unavailable');
            }
            notify('日志已复制到剪贴板。');
            addLog('info', '用户复制日志');
        } catch (error) {
            addLog('error', '复制日志失败', { message: String(error) });
            notify('复制日志失败，请打开控制台查看。');
        }
    }

    function clearLogs() {
        state.logs = [];
        addLog('info', '用户清空日志');
        refreshLogViewer();
    }

    function normalizeUrl(value) {
        if (!value || typeof value !== 'string') {
            return '';
        }
        try {
            return new URL(value.trim(), window.location.href).href;
        } catch {
            return '';
        }
    }

    function isXiaohongshuHost() {
        return /(^|\.)xiaohongshu\.com$/i.test(window.location.hostname || '');
    }

    function initXiaohongshuLinkEnhancer() {
        if (!isXiaohongshuHost() || window.__TMIE_XHS_LINK_ENHANCER_READY__) {
            return;
        }
        window.__TMIE_XHS_LINK_ENHANCER_READY__ = true;

        const processedTextNodes = new WeakMap();
        const queuedRoots = new Set();
        let flushScheduled = false;

        function injectXhsLinkStyle() {
            if (document.getElementById(XHS_LINK_HELPER.styleId)) {
                return;
            }

            const style = document.createElement('style');
            style.id = XHS_LINK_HELPER.styleId;
            style.textContent = `
                .${XHS_LINK_HELPER.linkClass} {
                    color: #12b76a !important;
                    text-decoration: underline !important;
                    word-break: break-all;
                }
            `;
            (document.head || document.documentElement).appendChild(style);
        }

        function cleanXhsSharedText(text) {
            let result = String(text || '');
            for (const pattern of XHS_LINK_HELPER.guidePatterns) {
                result = result.replace(pattern, '');
            }
            return result;
        }

        function splitDetectedUrlToken(value) {
            let urlText = String(value || '');
            let suffix = '';
            while (/[)\]}>.,;:!?，。；：！？、…]+$/.test(urlText)) {
                suffix = `${urlText.slice(-1)}${suffix}`;
                urlText = urlText.slice(0, -1);
            }
            return { urlText, suffix };
        }

        function shouldSkipXhsTextNode(node) {
            if (!node || node.nodeType !== Node.TEXT_NODE) {
                return true;
            }

            if (processedTextNodes.get(node) === node.textContent) {
                return true;
            }

            const parent = node.parentElement;
            if (!parent) {
                return true;
            }

            if (XHS_LINK_HELPER.skipTags.has(parent.tagName)) {
                return true;
            }

            if (parent.closest(`a, button, #${ROOT_ID}Modal, #${ROOT_ID}LogModal`)) {
                return true;
            }

            return false;
        }

        function buildXhsFragmentFromText(text) {
            const cleanedText = cleanXhsSharedText(text);
            const regex = XHS_LINK_HELPER.urlRegex;
            const fragment = document.createDocumentFragment();
            let lastIndex = 0;
            let hasUrl = false;
            let match;

            regex.lastIndex = 0;
            while ((match = regex.exec(cleanedText)) !== null) {
                const fullMatch = match[0];
                const start = match.index;
                const { urlText, suffix } = splitDetectedUrlToken(fullMatch);
                const normalizedUrl = normalizeUrl(urlText);

                if (start > lastIndex) {
                    fragment.appendChild(document.createTextNode(cleanedText.slice(lastIndex, start)));
                }

                if (normalizedUrl) {
                    const anchor = document.createElement('a');
                    anchor.href = normalizedUrl;
                    anchor.target = '_blank';
                    anchor.rel = 'noopener noreferrer';
                    anchor.className = XHS_LINK_HELPER.linkClass;
                    anchor.textContent = urlText;
                    fragment.appendChild(anchor);
                    if (suffix) {
                        fragment.appendChild(document.createTextNode(suffix));
                    }
                    hasUrl = true;
                } else {
                    fragment.appendChild(document.createTextNode(fullMatch));
                }

                lastIndex = start + fullMatch.length;
            }

            if (lastIndex < cleanedText.length) {
                fragment.appendChild(document.createTextNode(cleanedText.slice(lastIndex)));
            }

            if (!hasUrl && cleanedText === text) {
                return null;
            }

            if (!hasUrl) {
                fragment.textContent = cleanedText;
            }

            return fragment;
        }

        function processXhsTextNode(node) {
            if (shouldSkipXhsTextNode(node)) {
                return;
            }

            const originalText = node.textContent || '';
            if (!originalText.trim()) {
                processedTextNodes.set(node, originalText);
                return;
            }

            const fragment = buildXhsFragmentFromText(originalText);
            if (!fragment) {
                processedTextNodes.set(node, originalText);
                return;
            }

            node.replaceWith(fragment);
        }

        function processXhsContainer(container) {
            if (!(container instanceof HTMLElement)) {
                return;
            }

            const walker = document.createTreeWalker(
                container,
                NodeFilter.SHOW_TEXT,
                {
                    acceptNode(node) {
                        return shouldSkipXhsTextNode(node)
                            ? NodeFilter.FILTER_REJECT
                            : NodeFilter.FILTER_ACCEPT;
                    }
                }
            );

            const textNodes = [];
            let current = walker.nextNode();
            while (current) {
                textNodes.push(current);
                current = walker.nextNode();
            }

            for (const textNode of textNodes) {
                processXhsTextNode(textNode);
            }

            container.setAttribute(XHS_LINK_HELPER.markAttr, 'true');
        }

        function getXhsTargetContainers(root) {
            if (!(root instanceof Element || root instanceof Document)) {
                return [];
            }

            const containers = new Set();
            if (root instanceof Element) {
                for (const selector of XHS_LINK_HELPER.targetSelectors) {
                    if (root.matches(selector)) {
                        containers.add(root);
                    }
                    const closest = root.closest(selector);
                    if (closest) {
                        containers.add(closest);
                    }
                }
            }

            for (const selector of XHS_LINK_HELPER.targetSelectors) {
                const matches = root.querySelectorAll(selector);
                for (const element of matches) {
                    containers.add(element);
                }
            }

            return [...containers];
        }

        function processXhsRoot(root) {
            const containers = getXhsTargetContainers(root);
            for (const container of containers) {
                processXhsContainer(container);
            }
        }

        function enqueueXhsRoot(root) {
            const normalizedRoot = root instanceof Element || root instanceof Document
                ? root
                : root?.parentElement;
            if (!(normalizedRoot instanceof Element || normalizedRoot instanceof Document)) {
                return;
            }

            queuedRoots.add(normalizedRoot);
            if (flushScheduled) {
                return;
            }

            flushScheduled = true;
            requestAnimationFrame(() => {
                flushScheduled = false;
                const roots = [...queuedRoots];
                queuedRoots.clear();
                for (const queuedRoot of roots) {
                    processXhsRoot(queuedRoot);
                }
            });
        }

        function initXhsObserver() {
            if (!document.body) {
                return;
            }

            const observer = new MutationObserver((mutations) => {
                for (const mutation of mutations) {
                    if (mutation.type === 'characterData') {
                        enqueueXhsRoot(mutation.target);
                        continue;
                    }

                    if (mutation.type !== 'childList' || mutation.addedNodes.length === 0) {
                        continue;
                    }

                    for (const node of mutation.addedNodes) {
                        enqueueXhsRoot(node);
                    }
                }
            });

            observer.observe(document.body, {
                childList: true,
                subtree: true,
                characterData: true
            });
        }

        injectXhsLinkStyle();
        processXhsRoot(document);
        initXhsObserver();
        addLog('info', '小红书链接解析模块已启用');
    }

    function pickImageSource(img) {
        const directCandidates = [
            img.currentSrc,
            img.getAttribute('data-original'),
            img.getAttribute('data-src'),
            img.getAttribute('data-lazy-src'),
            img.getAttribute('data-url'),
            img.getAttribute('src')
        ];

        for (const candidate of directCandidates) {
            const normalized = normalizeUrl(candidate);
            if (normalized && !normalized.startsWith('data:')) {
                return normalized;
            }
        }

        const srcset = img.getAttribute('srcset') || img.getAttribute('data-srcset');
        if (!srcset) {
            return '';
        }

        const parsed = srcset
            .split(',')
            .map((part) => part.trim())
            .filter(Boolean)
            .map((part) => {
                const pieces = part.split(/\s+/);
                return {
                    url: normalizeUrl(pieces[0]),
                    width: Number.parseInt((pieces[1] || '').replace(/\D/g, ''), 10) || 0
                };
            })
            .filter((item) => item.url);

        parsed.sort((a, b) => b.width - a.width);
        return parsed[0]?.url || '';
    }

    function sanitizePathSegment(value, fallback, maxLength) {
        let sanitized = String(value || '')
            .normalize('NFKC')
            .replace(/[\u0000-\u001f\u007f]/g, '')
            .replace(/[\\/:*?"<>|]/g, ' ')
            .replace(/[\u200b-\u200f\uFEFF]/g, '')
            .replace(/['"`~!@#$%^&+=,;，。；：！？、【】《》〈〉「」『』（）()\[\]{}]/g, ' ')
            .replace(/[^\p{L}\p{N}\s._-]/gu, ' ')
            .replace(/[\s._-]+/g, '-')
            .replace(/^-+|-+$/g, '')
            .replace(/^\.+|\.+$/g, '');

        if (RESERVED_WINDOWS_NAMES.test(sanitized)) {
            sanitized = `file-${sanitized}`;
        }

        if (!sanitized) {
            sanitized = fallback;
        }

        if (sanitized.length > maxLength) {
            sanitized = sanitized.slice(0, maxLength).replace(/-+$/g, '');
        }

        return sanitized || fallback;
    }

    function normalizePlainText(value) {
        return String(value || '')
            .normalize('NFKC')
            .replace(/[\u200b-\u200f\uFEFF]/g, '')
            .replace(/\s+/g, ' ')
            .trim();
    }

    function stripEmojiAndSymbols(value) {
        return String(value || '')
            .replace(/[\u{1F300}-\u{1FAFF}\u{2600}-\u{27BF}]/gu, ' ')
            .replace(/[\u{FE00}-\u{FE0F}\u{1F1E6}-\u{1F1FF}]/gu, ' ')
            .replace(/[^\p{L}\p{N}\s]/gu, ' ');
    }

    function trimTitleByUnits(value, maxUnits) {
        let units = 0;
        let result = '';
        for (const char of String(value || '')) {
            const isAsciiWord = /[A-Za-z0-9]/.test(char);
            const weight = isAsciiWord ? 0.5 : 1;
            if ((units + weight) > maxUnits) {
                break;
            }
            result += char;
            units += weight;
        }
        return result.trim();
    }

    function cleanupTitleCandidate(value) {
        let cleaned = normalizePlainText(value);
        if (!cleaned) {
            return '';
        }

        cleaned = cleaned
            .replace(/[_\-|\s]*(站酷ZCOOL|站酷|ZCOOL|小红书|xiaohongshu|RED)$/i, '')
            .replace(/^[#＃]+\s*/, '')
            .replace(/[|｜丨]+/g, ' ')
            .replace(/\s+/g, ' ')
            .trim();

        if (cleaned.includes('#')) {
            const beforeTopic = cleaned.split('#')[0].trim();
            if (beforeTopic.length >= 4) {
                cleaned = beforeTopic;
            }
        }

        cleaned = cleaned
            .split(/\n+/)[0]
            .split(/[。！？!?.]/)[0]
            .trim();

        cleaned = stripEmojiAndSymbols(cleaned)
            .replace(/\b(notes?|post|feed|explore|热门|推荐|话题|标签)\b/gi, ' ')
            .replace(/\s+/g, ' ')
            .trim();

        cleaned = trimTitleByUnits(cleaned, MAX_TITLE_UNITS);
        return cleaned;
    }

    function isVisibleTextNode(node) {
        if (!node || !(node instanceof Element)) {
            return false;
        }
        const style = window.getComputedStyle(node);
        if (style.display === 'none' || style.visibility === 'hidden' || Number(style.opacity) === 0) {
            return false;
        }
        const rect = node.getBoundingClientRect();
        return rect.width > 0 && rect.height > 0;
    }

    function getTextBySelectors(selectors) {
        for (const selector of selectors) {
            const nodes = Array.from(document.querySelectorAll(selector));
            const candidates = nodes
                .filter(isVisibleTextNode)
                .map((node) => cleanupTitleCandidate(node.textContent || node.getAttribute?.('content')))
                .filter((text) => text && text.length >= 4 && text.length <= 40)
                .sort((left, right) => right.length - left.length);
            if (candidates[0]) {
                return candidates[0];
            }
        }
        return '';
    }

    function formatDateStamp(date) {
        const year = date.getFullYear();
        const month = String(date.getMonth() + 1).padStart(2, '0');
        const day = String(date.getDate()).padStart(2, '0');
        return `${year}${month}${day}`;
    }

    // 从 YYYYMMDD 取出 YYYY-MM 作为按月归档的上层目录。
    // 带横线是为了和下层的 YYYYMMDD-标题 在视觉上区分开，字典序仍然等于时间序。
    function formatMonthFolder(stamp) {
        const match = String(stamp || '').match(/^(\d{4})(\d{2})/);
        if (!match) {
            const now = new Date();
            return `${now.getFullYear()}-${String(now.getMonth() + 1).padStart(2, '0')}`;
        }
        return `${match[1]}-${match[2]}`;
    }

    function parseRelativeChineseDate(text) {
        const value = String(text || '').trim();
        const match = value.match(/(\d+)\s*(分钟|小时|天|周|个月|月|年)前/);
        if (!match) {
            return null;
        }

        const count = Number(match[1]);
        const unit = match[2];
        const date = new Date();
        if (unit === '分钟') {
            date.setMinutes(date.getMinutes() - count);
        } else if (unit === '小时') {
            date.setHours(date.getHours() - count);
        } else if (unit === '天') {
            date.setDate(date.getDate() - count);
        } else if (unit === '周') {
            date.setDate(date.getDate() - count * 7);
        } else if (unit === '个月' || unit === '月') {
            date.setMonth(date.getMonth() - count);
        } else if (unit === '年') {
            date.setFullYear(date.getFullYear() - count);
        }
        return date;
    }

    function parseDateCandidate(value) {
        if (!value) {
            return null;
        }

        const raw = String(value).trim();
        const directMatch = raw.match(/(\d{4})[年\-/.](\d{1,2})[月\-/.](\d{1,2})/);
        if (directMatch) {
            const year = Number(directMatch[1]);
            const month = Number(directMatch[2]) - 1;
            const day = Number(directMatch[3]);
            const date = new Date(year, month, day);
            if (!Number.isNaN(date.getTime())) {
                return date;
            }
        }

        const relative = parseRelativeChineseDate(raw);
        if (relative) {
            return relative;
        }

        const parsed = new Date(raw);
        if (!Number.isNaN(parsed.getTime())) {
            return parsed;
        }
        return null;
    }

    function extractJsonLdDates() {
        const result = [];
        const nodes = document.querySelectorAll('script[type="application/ld+json"]');
        for (const node of nodes) {
            const text = node.textContent?.trim();
            if (!text) {
                continue;
            }
            try {
                const data = JSON.parse(text);
                const list = Array.isArray(data) ? data : [data];
                for (const item of list) {
                    if (!item || typeof item !== 'object') {
                        continue;
                    }
                    const candidates = [item.datePublished, item.uploadDate, item.dateCreated, item.dateModified];
                    for (const candidate of candidates) {
                        if (candidate) {
                            result.push(candidate);
                        }
                    }
                }
            } catch {
                continue;
            }
        }
        return result;
    }

    function detectPagePublishDate() {
        const candidates = [];
        const metaSelectors = [
            'meta[property="og:release_date"]',
            'meta[property="article:published_time"]',
            'meta[property="og:published_time"]',
            'meta[name="publishdate"]',
            'meta[name="pubdate"]',
            'meta[name="date"]',
            'meta[itemprop="datePublished"]'
        ];

        for (const selector of metaSelectors) {
            const node = document.querySelector(selector);
            if (node?.content) {
                candidates.push({ source: selector, value: node.content });
            }
        }

        for (const value of extractJsonLdDates()) {
            candidates.push({ source: 'jsonld', value });
        }

        document.querySelectorAll('time[datetime], [title*="创建时间"], [title*="发布时间"], [data-time], [data-publish-time]')
            .forEach((node) => {
                const value = node.getAttribute('datetime')
                    || node.getAttribute('title')
                    || node.getAttribute('data-time')
                    || node.getAttribute('data-publish-time')
                    || node.textContent;
                if (value) {
                    candidates.push({ source: 'dom', value });
                }
            });

        const bodyTextCandidates = Array.from(document.querySelectorAll('span,div,p'))
            .map((node) => node.textContent?.trim())
            .filter(Boolean)
            .filter((text) => /(\d{4}[年\-/.]\d{1,2}[月\-/.]\d{1,2})|(\d+\s*(分钟|小时|天|周|个月|月|年)前)/.test(text))
            .slice(0, 30);
        for (const value of bodyTextCandidates) {
            candidates.push({ source: 'text', value });
        }

        for (const item of candidates) {
            const date = parseDateCandidate(item.value);
            if (date) {
                return {
                    stamp: formatDateStamp(date),
                    source: item.source,
                    raw: item.value
                };
            }
        }

        return {
            stamp: formatDateStamp(new Date()),
            source: 'fallback-now',
            raw: ''
        };
    }

    function readJsonLdTitles() {
        const titles = [];
        const nodes = document.querySelectorAll('script[type="application/ld+json"]');
        for (const node of nodes) {
            const text = node.textContent?.trim();
            if (!text) {
                continue;
            }
            try {
                const data = JSON.parse(text);
                const list = Array.isArray(data) ? data : [data];
                for (const item of list) {
                    if (!item || typeof item !== 'object') {
                        continue;
                    }
                    if (item.headline) {
                        titles.push(item.headline);
                    }
                    if (item.name) {
                        titles.push(item.name);
                    }
                }
            } catch {
                continue;
            }
        }
        return titles;
    }

    function detectPageTitle() {
        const preferredSelectors = [
            '#detail-title',
            '.note-content .title',
            '.note-content .desc',
            '[class*="note-content"] [class*="title"]',
            '[class*="note-content"] [class*="desc"]',
            'main h1',
            'article h1',
            'section h1',
            '[class*="note"] h1',
            '[class*="title"] h1',
            '[class*="title"]',
            '[data-testid*="title"]',
            '[class*="content"] [class*="title"]',
            '[class*="post"] [class*="title"]',
            'h1'
        ];

        const directTitle = getTextBySelectors(preferredSelectors);
        if (directTitle) {
            return directTitle;
        }

        const candidates = [
            document.querySelector('meta[property="og:title"]')?.content,
            ...readJsonLdTitles(),
            document.title,
            document.querySelector('meta[name="keywords"]')?.content
        ].filter(Boolean);

        for (const item of candidates) {
            const cleaned = cleanupTitleCandidate(item);
            if (cleaned) {
                return cleaned;
            }
        }
        return '未命名页面';
    }

    function getHostLabel() {
        const host = window.location.hostname.toLowerCase();
        if (SITE_NAME_MAP.has(host)) {
            return sanitizePathSegment(SITE_NAME_MAP.get(host), '站点', 20);
        }
        const shortHost = host.replace(/^www\./, '').split('.').slice(0, 2).join('-');
        return sanitizePathSegment(shortHost || host, 'site', 20);
    }

    function getPageMeta() {
        if (state.pageMeta) {
            return state.pageMeta;
        }

        const publish = detectPagePublishDate();
        const title = detectPageTitle();
        const monthFolder = formatMonthFolder(publish.stamp);
        const folderName = sanitizePathSegment(
            `${publish.stamp}-${title}`,
            `${publish.stamp}-未命名页面`,
            MAX_FOLDER_LENGTH
        );
        const meta = {
            publishDate: publish.stamp,
            publishDateSource: publish.source,
            publishDateRaw: publish.raw,
            titleRaw: title,
            titleLabel: sanitizePathSegment(title, '未命名页面', 48),
            hostLabel: getHostLabel(),
            monthFolder,
            folderName,
            folderPath: `${monthFolder}/${folderName}`
        };

        state.pageMeta = meta;
        addLog('info', '解析页面元信息', meta);
        return meta;
    }

    function guessExtension(src) {
        try {
            const url = new URL(src, window.location.href);
            const path = url.pathname.toLowerCase();
            const query = url.search.toLowerCase();
            const match = path.match(/\.(avif|bmp|gif|jpe?g|jfif|png|svg|webp)(?=$)/i)
                || query.match(/[?&](?:format|fmt|ext|type)=([a-z0-9]+)/i);
            const ext = (match?.[1] || '').toLowerCase();
            if (ext === 'jpeg' || ext === 'jfif') {
                return 'jpg';
            }
            if (['avif', 'bmp', 'gif', 'jpg', 'png', 'svg', 'webp'].includes(ext)) {
                return ext;
            }
        } catch {
            return 'jpg';
        }
        return 'jpg';
    }

    function buildDownloadPath(image, serial) {
        const meta = getPageMeta();
        const baseName = sanitizePathSegment(
            `${meta.publishDate}-${meta.hostLabel}-${meta.titleLabel}-${serial}`,
            `${meta.publishDate}-${meta.hostLabel}-${serial}`,
            MAX_FILE_LENGTH
        );
        return `${meta.folderPath}/${baseName}.${guessExtension(image.src)}`;
    }

    function readImageMetaFromDom(img, src) {
        const width = Number(img.naturalWidth) || 0;
        const height = Number(img.naturalHeight) || 0;
        if (!src || width <= 0 || height <= 0) {
            return null;
        }
        return { src, width, height };
    }

    function probeImageMeta(src) {
        return new Promise((resolve) => {
            if (!src) {
                resolve(null);
                return;
            }

            const image = new Image();
            let settled = false;
            const timer = window.setTimeout(() => {
                if (!settled) {
                    settled = true;
                    resolve(null);
                }
            }, PROBE_TIMEOUT);

            image.decoding = 'async';
            image.referrerPolicy = 'strict-origin-when-cross-origin';
            image.onload = () => {
                if (settled) {
                    return;
                }
                settled = true;
                window.clearTimeout(timer);
                resolve({
                    src,
                    width: Number(image.naturalWidth) || 0,
                    height: Number(image.naturalHeight) || 0
                });
            };
            image.onerror = () => {
                if (settled) {
                    return;
                }
                settled = true;
                window.clearTimeout(timer);
                resolve(null);
            };
            image.src = src;
        });
    }

    function getAbsoluteTop(node) {
        const rect = node.getBoundingClientRect();
        return rect.top + window.scrollY;
    }

    function isInsideExtractorUi(node) {
        return Boolean(node.closest?.(`[${UI_MARK_ATTR}]`));
    }

    function isLikelyContentImage(img) {
        if (!img.isConnected) {
            return false;
        }
        // 排除插件自身面板里的缩略图，否则重新扫描时会把自己的 DOM 也扫一遍
        if (isInsideExtractorUi(img)) {
            return false;
        }
        if (img.closest('header, nav, footer, aside')) {
            return false;
        }
        if (img.closest('[aria-hidden="true"]')) {
            return false;
        }
        const style = window.getComputedStyle(img);
        if (style.display === 'none' || style.visibility === 'hidden' || Number(style.opacity) === 0) {
            return false;
        }
        return true;
    }

    function getZcoolCutoffTop() {
        const candidate = document.querySelector('.recommendContentBox')
            || document.querySelector('.statementBox')
            || document.querySelector('.relatedRecommendWrap');
        if (candidate) {
            return getAbsoluteTop(candidate);
        }

        const likeNumber = Array.from(document.querySelectorAll('.likeNum, span, div'))
            .find((node) => /^\d+$/.test((node.textContent || '').trim()) && node.closest('div')?.querySelector('use[xlink\\:href="#icon-detail-like"], use[href="#icon-detail-like"]'));
        return likeNumber ? getAbsoluteTop(likeNumber) : Number.POSITIVE_INFINITY;
    }

    function getSiteRuleContext() {
        const host = window.location.hostname;
        const path = window.location.pathname;
        if (/zcool\.com\.cn$/i.test(host) && /^\/work\//.test(path)) {
            return {
                site: 'zcool-work',
                cutoffTop: getZcoolCutoffTop()
            };
        }
        return {
            site: 'generic',
            cutoffTop: Number.POSITIVE_INFINITY
        };
    }

    function shouldSkipBySiteRule(img, siteRule) {
        if (siteRule.site !== 'zcool-work') {
            return false;
        }
        const imgTop = getAbsoluteTop(img);
        return imgTop >= (siteRule.cutoffTop - 6);
    }

    // 去掉路径尾部的 CDN 规格后缀，但必须保证不会误删文件名本身。
    // 宁可少合并(留下重复卡片)，也不能多合并(丢图)。
    function stripSpecSuffix(pathname) {
        // photo.jpg@640w_480h.webp -> photo.jpg
        // 只有 @ 之前已经是个带图片扩展名的完整文件名时才敢删
        const atMatch = pathname.match(/^(.*\.(?:avif|bmp|gif|jpe?g|jfif|png|svg|webp))@[^/]*$/i);
        if (atMatch) {
            return atMatch[1];
        }

        // abc123!nd_dft_wlteh_webp_3 -> abc123
        // 要求 ! 之后不含点，否则可能是 IMG!front.jpg 这种真实文件名
        const bangMatch = pathname.match(/^(.*?)!([^/.]*)$/);
        if (bangMatch && bangMatch[1] && !bangMatch[1].endsWith('/')) {
            return bangMatch[1];
        }

        return pathname;
    }

    function buildDedupeKey(src) {
        try {
            const url = new URL(src, window.location.href);
            for (const param of SIZE_QUERY_PARAMS) {
                url.searchParams.delete(param);
            }
            url.hash = '';
            return `${url.origin}${stripSpecSuffix(url.pathname)}${url.search}`;
        } catch {
            return src;
        }
    }

    function collectBackgroundImageCandidates(siteRule) {
        const results = [];
        const nodes = document.querySelectorAll(BACKGROUND_SCAN_SELECTOR);
        const limit = Math.min(nodes.length, BACKGROUND_SCAN_LIMIT);

        for (let i = 0; i < limit; i += 1) {
            const node = nodes[i];
            const rect = node.getBoundingClientRect();
            // 元素本身太小的不可能承载大图，先用布局尺寸粗筛，避免全量 getComputedStyle
            if (rect.width < BACKGROUND_MIN_BOX || rect.height < BACKGROUND_MIN_BOX) {
                continue;
            }
            if (isInsideExtractorUi(node)) {
                continue;
            }
            if (node.closest('header, nav, footer, aside')) {
                continue;
            }
            if (shouldSkipBySiteRule(node, siteRule)) {
                continue;
            }

            const backgroundImage = window.getComputedStyle(node).backgroundImage;
            if (!backgroundImage || backgroundImage === 'none') {
                continue;
            }

            for (const match of backgroundImage.matchAll(/url\((['"]?)([^'")]+)\1\)/g)) {
                const normalized = normalizeUrl(match[2]);
                if (normalized && !normalized.startsWith('data:')) {
                    results.push({ src: normalized, alt: '' });
                }
            }
        }

        return results;
    }

    function collectPictureSourceCandidates() {
        const results = [];
        for (const source of document.querySelectorAll('picture source[srcset], picture source[src]')) {
            if (isInsideExtractorUi(source)) {
                continue;
            }
            const raw = source.getAttribute('srcset') || source.getAttribute('src') || '';
            for (const part of raw.split(',')) {
                const token = part.trim().split(/\s+/)[0];
                const normalized = normalizeUrl(token);
                if (normalized && !normalized.startsWith('data:')) {
                    results.push({ src: normalized, alt: '' });
                }
            }
        }
        return results;
    }

    async function collectAllImages() {
        state.pageMeta = null;
        getPageMeta();
        showLoading('正在扫描页面中的大图，请稍候…');
        addLog('info', '开始扫描图片', {
            url: window.location.href,
            host: window.location.hostname,
            title: document.title
        });

        state.selectedImages.clear();

        const siteRule = getSiteRuleContext();
        addLog('info', '站点规则已加载', siteRule);

        const imgNodes = Array.from(document.images);
        const uniqueMap = new Map();
        const seenSources = new Set();
        const candidates = [];
        let skippedByDom = 0;
        let skippedBySite = 0;
        let skippedBySize = 0;
        let skippedByPluginUi = 0;
        let skippedWithoutProbe = 0;
        let skippedBySuppressedSize = 0;
        const suppressedSizeCounts = new Map();

        for (const img of imgNodes) {
            if (isInsideExtractorUi(img)) {
                skippedByPluginUi += 1;
                continue;
            }
            if (!isLikelyContentImage(img)) {
                skippedByDom += 1;
                continue;
            }
            if (shouldSkipBySiteRule(img, siteRule)) {
                skippedBySite += 1;
                continue;
            }
            const src = pickImageSource(img);
            if (!src || src.startsWith('data:')) {
                skippedByDom += 1;
                continue;
            }
            if (seenSources.has(src)) {
                continue;
            }
            seenSources.add(src);
            candidates.push({
                src,
                node: img,
                // 取到的 URL 正是浏览器已加载完成的那个，naturalWidth 可信
                exactLoaded: Boolean(img.complete && img.currentSrc && src === normalizeUrl(img.currentSrc)),
                alt: (img.getAttribute('alt') || img.getAttribute('title') || '').trim()
            });
        }

        const extraCandidates = [
            ...collectPictureSourceCandidates(),
            ...collectBackgroundImageCandidates(siteRule)
        ];
        let backgroundFound = 0;
        for (const candidate of extraCandidates) {
            if (seenSources.has(candidate.src)) {
                continue;
            }
            seenSources.add(candidate.src);
            backgroundFound += 1;
            candidates.push({ src: candidate.src, node: null, alt: candidate.alt });
        }

        await mapWithConcurrency(candidates, PROBE_CONCURRENCY, async (candidate, index) => {
            const candidateKey = buildDedupeKey(candidate.src);

            // 上次访问已记下这个图的尺寸，且该尺寸正被记忆隐藏 —— 连探测都不用发
            const cachedSize = state.sizeCache.get(candidateKey);
            if (cachedSize && state.suppressedSizes.has(cachedSize)) {
                skippedBySuppressedSize += 1;
                skippedWithoutProbe += 1;
                suppressedSizeCounts.set(cachedSize, (suppressedSizeCounts.get(cachedSize) || 0) + 1);
                return;
            }

            const domMeta = candidate.node
                ? readImageMetaFromDom(candidate.node, candidate.src)
                : null;
            const minSize = state.minSize;
            let meta = null;

            if (domMeta && domMeta.width >= minSize && domMeta.height >= minSize) {
                meta = domMeta;
            } else if (domMeta && candidate.exactLoaded) {
                // 浏览器已按这个 URL 加载完成，naturalWidth 就是它的真实尺寸，
                // 再探测一次只会拿到同样的值，直接判定为不合格
                skippedBySize += 1;
                skippedWithoutProbe += 1;
                return;
            } else {
                meta = await probeImageMeta(candidate.src);
            }

            if (!meta || meta.width < minSize || meta.height < minSize) {
                skippedBySize += 1;
                if (meta) {
                    state.sizeCache.set(candidateKey, `${meta.width}x${meta.height}`);
                }
                return;
            }

            const sizeKey = `${meta.width}x${meta.height}`;
            state.sizeCache.set(candidateKey, sizeKey);

            // 已记忆为隐藏的尺寸不进 allImages，也就不会建卡片/加载缩略图
            if (state.suppressedSizes.has(sizeKey)) {
                skippedBySuppressedSize += 1;
                suppressedSizeCounts.set(sizeKey, (suppressedSizeCounts.get(sizeKey) || 0) + 1);
                return;
            }

            const dedupeKey = buildDedupeKey(meta.src);
            const existing = uniqueMap.get(dedupeKey);
            const current = {
                src: meta.src,
                width: meta.width,
                height: meta.height,
                sizeKey: `${meta.width}x${meta.height}`,
                alt: candidate.alt,
                index
            };

            if (!existing) {
                uniqueMap.set(dedupeKey, current);
                return;
            }

            // 同一张图的不同规格，保留像素面积最大的那个 URL
            if ((current.width * current.height) > (existing.width * existing.height)) {
                uniqueMap.set(dedupeKey, {
                    ...current,
                    alt: current.alt || existing.alt,
                    index: Math.min(current.index, existing.index)
                });
                return;
            }

            if (!existing.alt && current.alt) {
                existing.alt = current.alt;
            }
        });

        state.allImages = Array.from(uniqueMap.values()).sort((a, b) => a.index - b.index);
        state.imageOrder = new Map(state.allImages.map((image, order) => [image.src, order]));
        state.suppressedSizeCounts = suppressedSizeCounts;
        persistSizeCache();
        resetGalleryDom();
        applyFilters(false);
        hideLoading();
        renderModal();
        addLog('info', '扫描完成', {
            totalImgElements: imgNodes.length,
            pageImgElements: imgNodes.length - skippedByPluginUi,
            candidates: candidates.length,
            fromBackgroundOrSource: backgroundFound,
            extracted: state.allImages.length,
            skippedByDom,
            skippedBySite,
            skippedBySize,
            skippedWithoutProbe,
            skippedBySuppressedSize,
            suppressedSizes: Object.fromEntries(suppressedSizeCounts)
        });
    }

    function getVisibleSizeOptions() {
        const sizeMap = new Map();
        for (const image of state.allImages) {
            sizeMap.set(image.sizeKey, image);
        }
        // 扫描阶段被记忆跳过的尺寸没进 allImages，也要列出来才能恢复
        for (const sizeKey of state.suppressedSizeCounts.keys()) {
            if (!sizeMap.has(sizeKey)) {
                sizeMap.set(sizeKey, null);
            }
        }
        return Array.from(sizeMap.keys()).sort((left, right) => {
            const [leftWidth, leftHeight] = left.split('x').map(Number);
            const [rightWidth, rightHeight] = right.split('x').map(Number);
            const rightArea = rightWidth * rightHeight;
            const leftArea = leftWidth * leftHeight;
            return rightArea - leftArea || rightWidth - leftWidth || rightHeight - leftHeight;
        });
    }

    function applyFilters(render = true) {
        state.filteredImages = state.allImages.filter((image) => !state.suppressedSizes.has(image.sizeKey));
        if (render) {
            renderModal();
        }
    }

    // mode: 'select' | 'deselect' | 'invert'
    function setSelectionForFiltered(mode) {
        for (const image of state.filteredImages) {
            const nextSelected = mode === 'invert'
                ? !state.selectedImages.has(image.src)
                : mode === 'select';

            if (nextSelected) {
                state.selectedImages.add(image.src);
            } else {
                state.selectedImages.delete(image.src);
            }
        }

        // 只改视觉状态，不重建 DOM
        const gallery = document.getElementById(`${ROOT_ID}Gallery`);
        if (gallery) {
            for (const card of gallery.querySelectorAll(`.${ROOT_ID}Card`)) {
                applyCardSelectionState(card, state.selectedImages.has(card.dataset.src || ''));
            }
        }
        renderStats();
    }

    function selectAllFilteredImages() {
        addLog('info', '用户全选当前结果', { count: state.filteredImages.length });
        setSelectionForFiltered('select');
    }

    function deselectAllFilteredImages() {
        addLog('info', '用户取消全选当前结果', { count: state.filteredImages.length });
        setSelectionForFiltered('deselect');
    }

    function invertSelectionForFiltered() {
        addLog('info', '用户反选当前结果', { count: state.filteredImages.length });
        setSelectionForFiltered('invert');
    }

    function persistSuppressedSizes() {
        storeValue(STORAGE_KEYS.hiddenSizes, Array.from(state.suppressedSizes));
    }

    // 被记忆隐藏的尺寸在扫描阶段就没被收集，恢复显示时内存里没有数据，必须重扫
    function needsRescanToReveal(sizeKeys) {
        return sizeKeys.some((key) => state.suppressedSizeCounts.has(key));
    }

    function afterSuppressedSizesChanged(revealedKeys) {
        persistSuppressedSizes();
        if (needsRescanToReveal(revealedKeys)) {
            addLog('info', '恢复显示的尺寸需要重新扫描才能取回', { sizes: revealedKeys });
            collectAllImages();
            return;
        }
        applyFilters();
    }

    function toggleSuppressedSize(sizeKey) {
        let revealed = [];
        if (state.suppressedSizes.has(sizeKey)) {
            state.suppressedSizes.delete(sizeKey);
            revealed = [sizeKey];
            addLog('info', '用户显示尺寸', { size: sizeKey });
        } else {
            state.suppressedSizes.add(sizeKey);
            addLog('info', '用户隐藏尺寸', { size: sizeKey });
        }
        afterSuppressedSizesChanged(revealed);
    }

    function showAllSuppressedSizes() {
        const revealed = Array.from(state.suppressedSizes);
        state.suppressedSizes.clear();
        addLog('info', '用户显示全部尺寸');
        afterSuppressedSizesChanged(revealed);
    }

    function resetDefaultSuppressedSizes() {
        const revealed = Array.from(state.suppressedSizes)
            .filter((key) => !DEFAULT_HIDDEN_SIZES.has(key));
        state.suppressedSizes = new Set(DEFAULT_HIDDEN_SIZES);
        addLog('info', '用户恢复默认隐藏尺寸');
        afterSuppressedSizesChanged(revealed);
    }

    function closeModal() {
        document.getElementById(`${ROOT_ID}Modal`)?.remove();
    }

    function closeLogViewer() {
        document.getElementById(`${ROOT_ID}LogModal`)?.remove();
        state.showLogViewer = false;
    }

    function getDownloadModeHint() {
        const handler = GM_info?.scriptHandler || 'Tampermonkey';
        const browserInfo = navigator.userAgent;
        const mode = GM_info?.downloadMode || 'unknown';
        const subfolderHint = /chrome/i.test(browserInfo)
            ? 'Chrome 下如需自动创建子文件夹，请确认 Tampermonkey 设置中的 Downloads mode 为 Browser API。'
            : '当前浏览器是否支持自动子文件夹，取决于脚本管理器下载模式。';
        return { handler, mode, subfolderHint };
    }

    function closeAllPopovers(root, exceptId) {
        for (const pop of root.querySelectorAll(`.${ROOT_ID}Pop`)) {
            if (pop.id === exceptId) {
                continue;
            }
            pop.hidden = true;
            const trigger = root.querySelector(`[aria-controls="${pop.id}"]`);
            trigger?.setAttribute('aria-expanded', 'false');
        }
    }

    function bindPopover(root, triggerId, popId) {
        const trigger = root.querySelector(`#${triggerId}`);
        const pop = root.querySelector(`#${popId}`);
        if (!trigger || !pop) {
            return;
        }

        trigger.setAttribute('aria-controls', popId);

        trigger.addEventListener('click', (event) => {
            event.stopPropagation();
            const willOpen = pop.hidden;
            closeAllPopovers(root);
            pop.hidden = !willOpen;
            trigger.setAttribute('aria-expanded', willOpen ? 'true' : 'false');
        });

        // 点菜单里的按钮后收起，但输入框、提示文字、尺寸筛选按钮不收起
        // （尺寸按钮用的是 FilterBtn，便于连续切换多个尺寸）
        // 同样用 composedPath：按钮的处理函数可能已经把自己从 DOM 里换掉了
        pop.addEventListener('click', (event) => {
            const path = typeof event.composedPath === 'function' ? event.composedPath() : [];
            const hitButton = path.length > 0
                ? path.some((node) => node?.classList?.contains?.(`${ROOT_ID}Btn`))
                : Boolean(event.target.closest?.(`.${ROOT_ID}Btn`));

            if (hitButton) {
                pop.hidden = true;
                trigger.setAttribute('aria-expanded', 'false');
            }
        });
    }

    function bindPopoverDismiss(root) {
        root.addEventListener('click', (event) => {
            // 用 composedPath 而不是 closest：弹层里的按钮（如尺寸筛选）点击后会
            // 同步重建 DOM，等事件冒泡到这里时 event.target 已经脱离文档，
            // closest() 会返回 null，导致刚点过的弹层被误判成「点了外部」而收起。
            // composedPath 在派发时就已固定，不受中途 DOM 变动影响。
            const path = typeof event.composedPath === 'function' ? event.composedPath() : [];
            const insideControl = path.length > 0
                ? path.some((node) => node?.classList?.contains?.(`${ROOT_ID}PopWrap`)
                    || node?.classList?.contains?.(`${ROOT_ID}Field`))
                : Boolean(event.target.closest?.(`.${ROOT_ID}PopWrap, .${ROOT_ID}Field`));

            // Field 是「最小尺寸 + ▾」的整体，点它的输入框也不该收起设置弹层
            if (!insideControl) {
                closeAllPopovers(root);
            }
        });

        root.addEventListener('keydown', (event) => {
            if (event.key !== 'Escape') {
                return;
            }
            const open = root.querySelector(`.${ROOT_ID}Pop:not([hidden])`);
            if (open) {
                event.stopPropagation();
                closeAllPopovers(root);
                root.querySelector(`[aria-controls="${open.id}"]`)?.focus();
            }
        });
    }

    function ensureModalShell() {
        let modal = document.getElementById(`${ROOT_ID}Modal`);
        if (modal) {
            return modal;
        }

        injectPanelCss();
        modal = document.createElement('div');
        modal.id = `${ROOT_ID}Modal`;
        modal.setAttribute(UI_MARK_ATTR, '1');
        modal.innerHTML = `
            <div id="${ROOT_ID}Panel">
                <div id="${ROOT_ID}Header">
                    <div>
                        <h2>图像提取工具 V${VERSION}</h2>
                        <p>单击卡片选择，双击看原图。下载命名为“日期-网站-标题-序号”。</p>
                    </div>
                    <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}Close">关闭</button>
                </div>
                <div id="${ROOT_ID}Toolbar">
                    <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}Refresh">重新扫描</button>

                    <div class="${ROOT_ID}Split">
                        <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}SelectAll">全选当前结果</button>
                        <div class="${ROOT_ID}PopWrap">
                            <button type="button" class="${ROOT_ID}Btn ${ROOT_ID}Caret" id="${ROOT_ID}SelectMenuBtn"
                                title="更多选择方式" aria-label="更多选择方式"
                                aria-expanded="false" aria-haspopup="true">▾</button>
                            <div class="${ROOT_ID}Pop" id="${ROOT_ID}SelectMenu" hidden>
                                <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}InvertSelect">反选</button>
                                <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}DeselectAll">取消全选</button>
                                <p class="${ROOT_ID}PopHint">反选会把当前显示的图片中已选与未选互换。</p>
                            </div>
                        </div>
                    </div>

                    <label class="${ROOT_ID}Chip" for="${ROOT_ID}StartIndex">起始序号</label>
                    <input type="number" id="${ROOT_ID}StartIndex" min="1" value="1" inputmode="numeric">
                    <button type="button" class="${ROOT_ID}Btn primary" id="${ROOT_ID}Download">下载选中图片</button>

                    <div class="${ROOT_ID}Field">
                        <label for="${ROOT_ID}MinSize">最小尺寸</label>
                        <input type="number" id="${ROOT_ID}MinSize" min="${MIN_SIZE_LIMITS.min}" max="${MIN_SIZE_LIMITS.max}"
                            step="50" value="${state.minSize}" inputmode="numeric">
                        <div class="${ROOT_ID}PopWrap">
                            <button type="button" class="${ROOT_ID}Btn ${ROOT_ID}Caret" id="${ROOT_ID}SettingsBtn"
                                title="更多扫描与下载设置" aria-label="更多扫描与下载设置"
                                aria-expanded="false" aria-haspopup="true">▾</button>
                            <div class="${ROOT_ID}Pop" id="${ROOT_ID}SettingsMenu" hidden>
                                <p class="${ROOT_ID}PopHint">宽高都不小于最小尺寸的图片才会被提取，改动后会自动重新扫描。</p>
                                <div class="${ROOT_ID}PopDivider"></div>
                                <div class="${ROOT_ID}PopRow">
                                    <label for="${ROOT_ID}DownloadDelay">下载间隔</label>
                                    <input type="number" id="${ROOT_ID}DownloadDelay" min="${DOWNLOAD_DELAY_LIMITS.min}" max="${DOWNLOAD_DELAY_LIMITS.max}"
                                        step="100" value="${state.downloadDelay}" inputmode="numeric">
                                </div>
                                <p class="${ROOT_ID}PopHint">每张图片下载之间等待的毫秒数，设为 0 则不等待。</p>
                            </div>
                        </div>
                    </div>

                    <div class="${ROOT_ID}PopWrap">
                        <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}SizeMenuBtn"
                            title="查看并筛选已识别的图片尺寸" aria-expanded="false" aria-haspopup="true">尺寸筛选 ▾</button>
                        <div class="${ROOT_ID}Pop wide" id="${ROOT_ID}SizeMenu" hidden>
                            <div id="${ROOT_ID}FilterButtons"></div>
                            <div class="${ROOT_ID}PopDivider"></div>
                            <div class="${ROOT_ID}PopRow">
                                <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}ShowAllSizes">显示全部尺寸</button>
                                <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}ResetSizes">恢复默认隐藏</button>
                            </div>
                            <p class="${ROOT_ID}PopHint">点击尺寸可切换显示或隐藏。隐藏的尺寸会被记住，下次访问同类页面时直接跳过，不再下载缩略图。</p>
                        </div>
                    </div>

                    <div class="${ROOT_ID}PopWrap">
                        <button type="button" class="${ROOT_ID}Btn ghost" id="${ROOT_ID}InfoBtn"
                            title="页面信息与下载模式" aria-expanded="false" aria-haspopup="true">信息 ▾</button>
                        <div class="${ROOT_ID}Pop alignRight" id="${ROOT_ID}InfoMenu" hidden>
                            <div id="${ROOT_ID}MetaTips" class="${ROOT_ID}PopList"></div>
                            <div class="${ROOT_ID}PopDivider"></div>
                            <div class="${ROOT_ID}PopRow">
                                <button type="button" class="${ROOT_ID}Btn ${state.loggingEnabled ? 'success' : ''}" id="${ROOT_ID}ToggleLog">${state.loggingEnabled ? '日志已开启' : '开启日志'}</button>
                                <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}OpenLog">查看日志</button>
                            </div>
                        </div>
                    </div>

                    <div id="${ROOT_ID}Stats"></div>
                </div>
            </div>
            <div id="${ROOT_ID}Gallery"></div>
        `;

        modal.addEventListener('click', (event) => {
            if (event.target === modal) {
                closeModal();
            }
        });

        modal.querySelector(`#${ROOT_ID}Close`).addEventListener('click', closeModal);
        modal.querySelector(`#${ROOT_ID}Refresh`).addEventListener('click', () => {
            addLog('info', '用户点击重新扫描');
            collectAllImages();
        });
        modal.querySelector(`#${ROOT_ID}SelectAll`).addEventListener('click', selectAllFilteredImages);
        modal.querySelector(`#${ROOT_ID}DeselectAll`).addEventListener('click', deselectAllFilteredImages);
        modal.querySelector(`#${ROOT_ID}InvertSelect`).addEventListener('click', invertSelectionForFiltered);
        modal.querySelector(`#${ROOT_ID}Download`).addEventListener('click', downloadSelectedImages);
        modal.querySelector(`#${ROOT_ID}ToggleLog`).addEventListener('click', toggleLoggingEnabled);
        modal.querySelector(`#${ROOT_ID}OpenLog`).addEventListener('click', openLogViewer);
        modal.querySelector(`#${ROOT_ID}ShowAllSizes`).addEventListener('click', showAllSuppressedSizes);
        modal.querySelector(`#${ROOT_ID}ResetSizes`).addEventListener('click', resetDefaultSuppressedSizes);

        bindPopover(modal, `${ROOT_ID}SelectMenuBtn`, `${ROOT_ID}SelectMenu`);
        bindPopover(modal, `${ROOT_ID}SettingsBtn`, `${ROOT_ID}SettingsMenu`);
        bindPopover(modal, `${ROOT_ID}InfoBtn`, `${ROOT_ID}InfoMenu`);
        bindPopover(modal, `${ROOT_ID}SizeMenuBtn`, `${ROOT_ID}SizeMenu`);
        bindPopoverDismiss(modal);

        const minSizeInput = modal.querySelector(`#${ROOT_ID}MinSize`);
        minSizeInput.addEventListener('change', () => {
            const next = clampNumber(
                Number.parseInt(minSizeInput.value, 10) || DEFAULT_MIN_SIZE,
                MIN_SIZE_LIMITS.min,
                MIN_SIZE_LIMITS.max
            );
            minSizeInput.value = String(next);
            if (next === state.minSize) {
                return;
            }
            state.minSize = next;
            storeValue(STORAGE_KEYS.minSize, next);
            addLog('info', '用户修改最小尺寸，重新扫描', { minSize: next });
            collectAllImages();
        });

        const delayInput = modal.querySelector(`#${ROOT_ID}DownloadDelay`);
        delayInput.addEventListener('change', () => {
            const next = clampNumber(
                Number.parseInt(delayInput.value, 10) || 0,
                DOWNLOAD_DELAY_LIMITS.min,
                DOWNLOAD_DELAY_LIMITS.max
            );
            delayInput.value = String(next);
            state.downloadDelay = next;
            storeValue(STORAGE_KEYS.downloadDelay, next);
            addLog('info', '用户修改下载间隔', { downloadDelay: next });
        });

        document.body.appendChild(modal);
        return modal;
    }

    function renderStats() {
        const statsNode = document.getElementById(`${ROOT_ID}Stats`);
        if (!statsNode) {
            return;
        }

        const selectedCount = state.selectedImages.size;
        const hiddenCount = state.allImages.length - state.filteredImages.length;
        let skippedTotal = 0;
        for (const count of state.suppressedSizeCounts.values()) {
            skippedTotal += count;
        }

        // 收进一个 chip：显示数/识别数，隐藏与跳过只在非零时补充
        const parts = [`显示 ${state.filteredImages.length} / ${state.allImages.length} 张`];
        if (hiddenCount > 0) {
            parts.push(`隐藏 ${hiddenCount}`);
        }
        if (skippedTotal > 0) {
            parts.push(`跳过 ${skippedTotal}`);
        }

        const selectedChip = selectedCount > 0
            ? `<span class="${ROOT_ID}Chip accent">已选中 ${selectedCount} 张</span>`
            : `<span class="${ROOT_ID}Chip">未选中</span>`;

        statsNode.innerHTML = `
            <span class="${ROOT_ID}Chip" title="识别总数 ${state.allImages.length} 张${hiddenCount ? `，被尺寸筛选隐藏 ${hiddenCount} 张` : ''}${skippedTotal ? `，按尺寸记忆跳过 ${skippedTotal} 张` : ''}">${parts.join(' · ')}</span>
            ${selectedChip}
        `;
    }

    function renderMetaTips() {
        const metaNode = document.getElementById(`${ROOT_ID}MetaTips`);
        if (!metaNode) {
            return;
        }

        const meta = getPageMeta();
        const downloadHint = getDownloadModeHint();
        metaNode.innerHTML = `
            <span class="${ROOT_ID}Chip success">命名日期：${escapeHtml(meta.publishDate)}（来源：${escapeHtml(meta.publishDateSource)}）</span>
            <span class="${ROOT_ID}Chip">文件夹：${escapeHtml(meta.folderPath)}</span>
            <span class="${ROOT_ID}Chip warn">下载模式：${escapeHtml(downloadHint.mode)}</span>
            <p class="${ROOT_ID}PopHint">${escapeHtml(downloadHint.subfolderHint)}</p>
        `;
    }

    // 按钮收起时也要能看出里面有多少尺寸、有没有被隐藏的
    function renderSizeMenuLabel(sizeKeys) {
        const trigger = document.getElementById(`${ROOT_ID}SizeMenuBtn`);
        if (!trigger) {
            return;
        }

        const hiddenCount = sizeKeys.filter((key) => state.suppressedSizes.has(key)).length;
        const parts = [`尺寸筛选 ${sizeKeys.length}`];
        if (hiddenCount > 0) {
            parts.push(`隐藏 ${hiddenCount}`);
        }
        trigger.textContent = `${parts.join(' · ')} ▾`;
        trigger.title = sizeKeys.length === 0
            ? '当前没有可筛选的尺寸'
            : `共识别出 ${sizeKeys.length} 种尺寸${hiddenCount ? `，其中 ${hiddenCount} 种已隐藏` : ''}，点击查看并筛选`;
    }

    function renderFilterButtons() {
        const root = document.getElementById(`${ROOT_ID}FilterButtons`);
        if (!root) {
            return;
        }

        const sizeKeys = getVisibleSizeOptions();
        renderSizeMenuLabel(sizeKeys);

        root.innerHTML = '';
        for (const sizeKey of sizeKeys) {
            const suppressed = state.suppressedSizes.has(sizeKey);
            const skippedCount = state.suppressedSizeCounts.get(sizeKey) || 0;
            const btn = document.createElement('button');
            btn.type = 'button';
            btn.className = `${ROOT_ID}FilterBtn ${suppressed ? 'suppressed' : 'visible'}`;
            if (!suppressed) {
                btn.textContent = sizeKey;
                btn.title = '当前显示，点击后隐藏';
            } else if (skippedCount > 0) {
                btn.textContent = `${sizeKey} · 跳过 ${skippedCount} 张（点此取回）`;
                btn.title = '扫描时已按记忆跳过，点击后重新扫描并显示';
            } else {
                btn.textContent = `${sizeKey}（点此显示）`;
                btn.title = '当前隐藏，点击后显示';
            }
            btn.dataset.size = sizeKey;
            btn.addEventListener('click', () => toggleSuppressedSize(sizeKey));
            root.appendChild(btn);
        }
    }

    function getGalleryRowMetrics(gallery) {
        const styles = window.getComputedStyle(gallery);
        const rowHeight = Number.parseFloat(styles.gridAutoRows) || 8;
        const rowGap = Number.parseFloat(styles.rowGap) || 0;
        return { rowHeight, rowGap };
    }

    let masonryResizeScheduled = false;

    function scheduleMasonryResize() {
        if (masonryResizeScheduled) {
            return;
        }
        masonryResizeScheduled = true;
        requestAnimationFrame(() => {
            masonryResizeScheduled = false;
            resizeMasonryGallery();
        });
    }

    function computeCardSpan(contentHeight, rowHeight, rowGap) {
        return Math.max(1, Math.ceil((contentHeight + rowGap) / (rowHeight + rowGap)));
    }

    function resizeMasonryGallery() {
        const gallery = document.getElementById(`${ROOT_ID}Gallery`);
        if (!gallery) {
            return;
        }

        // 一次读全部高度，再一次写全部 span，避免读写交替触发强制同步重排
        const metrics = getGalleryRowMetrics(gallery);
        const cards = gallery.querySelectorAll(`.${ROOT_ID}Card:not([hidden]), .${ROOT_ID}Empty:not([hidden])`);
        const spans = new Array(cards.length);

        for (let i = 0; i < cards.length; i += 1) {
            spans[i] = computeCardSpan(cards[i].getBoundingClientRect().height, metrics.rowHeight, metrics.rowGap);
        }

        for (let i = 0; i < cards.length; i += 1) {
            cards[i].style.gridRowEnd = `span ${spans[i]}`;
        }
    }

    function applyCardSelectionState(card, isSelected) {
        card.classList.toggle('selected', isSelected);
        card.setAttribute('aria-pressed', isSelected ? 'true' : 'false');
        const icon = card.querySelector(`.${ROOT_ID}SelectStateIcon`);
        const text = card.querySelector(`.${ROOT_ID}SelectStateText`);
        if (icon) {
            icon.innerHTML = isSelected ? '&#10003;' : '+';
        }
        if (text) {
            text.textContent = isSelected ? '已选中' : '点击选择';
        }
    }

    function toggleCardSelection(card) {
        const src = card.dataset.src || '';
        if (!src) {
            return;
        }
        const nextSelected = !state.selectedImages.has(src);
        if (nextSelected) {
            state.selectedImages.add(src);
        } else {
            state.selectedImages.delete(src);
        }
        applyCardSelectionState(card, nextSelected);
        renderStats();
    }

    function bindGalleryDelegates(gallery) {
        if (gallery.dataset.tmieBound === '1') {
            return;
        }
        gallery.dataset.tmieBound = '1';

        gallery.addEventListener('click', (event) => {
            const card = event.target.closest(`.${ROOT_ID}Card`);
            if (card && gallery.contains(card)) {
                toggleCardSelection(card);
            }
        });

        gallery.addEventListener('dblclick', (event) => {
            const card = event.target.closest(`.${ROOT_ID}Card`);
            if (!card || !gallery.contains(card)) {
                return;
            }
            event.preventDefault();
            const src = card.dataset.src || '';
            addLog('debug', '用户双击打开原图', { src });
            window.open(src, '_blank', 'noopener');
        });

        gallery.addEventListener('keydown', (event) => {
            if (event.key !== 'Enter' && event.key !== ' ') {
                return;
            }
            const card = event.target.closest(`.${ROOT_ID}Card`);
            if (card && gallery.contains(card)) {
                event.preventDefault();
                toggleCardSelection(card);
            }
        });

        // 缩略图尺寸就绪后统一重排一次，load/error 不冒泡故用捕获阶段
        gallery.addEventListener('load', scheduleMasonryResize, true);
        gallery.addEventListener('error', scheduleMasonryResize, true);
    }

    function resetGalleryDom() {
        const gallery = document.getElementById(`${ROOT_ID}Gallery`);
        if (!gallery) {
            return;
        }
        for (const card of gallery.querySelectorAll(`.${ROOT_ID}Card`)) {
            card.remove();
        }
    }

    function createCardElement(image, order) {
        const isSelected = state.selectedImages.has(image.src);
        const ratio = image.width > 0 && image.height > 0
            ? `${image.width} / ${image.height}`
            : 'auto';

        const card = document.createElement('article');
        card.className = `${ROOT_ID}Card${isSelected ? ' selected' : ''}`;
        card.dataset.src = image.src;
        card.dataset.order = String(order);
        card.setAttribute('role', 'button');
        card.setAttribute('tabindex', '0');
        card.setAttribute('aria-pressed', isSelected ? 'true' : 'false');
        card.innerHTML = `
            <div class="${ROOT_ID}ThumbWrap" style="--tmie-image-ratio: ${ratio};">
                <img class="${ROOT_ID}Thumb" src="${escapeHtml(image.src)}" alt="${escapeHtml(image.alt || '图片预览')}" loading="lazy" decoding="async">
            </div>
            <div class="${ROOT_ID}CardBody">
                <p class="${ROOT_ID}Meta">尺寸：${image.width} × ${image.height}</p>
                <div class="${ROOT_ID}SelectState">
                    <span class="${ROOT_ID}SelectStateIcon">${isSelected ? '&#10003;' : '+'}</span>
                    <span class="${ROOT_ID}SelectStateText">${isSelected ? '已选中' : '点击选择'}</span>
                </div>
            </div>
        `;
        return card;
    }

    function ensureEmptyNode(gallery) {
        let empty = gallery.querySelector(`.${ROOT_ID}Empty`);
        if (!empty) {
            empty = document.createElement('div');
            empty.className = `${ROOT_ID}Empty`;
            empty.innerHTML = `
                <strong>当前没有符合条件的图片。</strong>
                <p>可以尝试重新扫描，或者点击对应尺寸按钮恢复显示。</p>
            `;
            gallery.prepend(empty);
        }
        return empty;
    }

    // 只为当前可见(未被尺寸过滤)的图片建卡片。被记忆隐藏的尺寸完全不进 DOM，
    // 也就不会加载缩略图；之后恢复显示时再按原始顺序补插进去。
    function syncGalleryCards(gallery) {
        const existing = new Map();
        for (const card of gallery.querySelectorAll(`.${ROOT_ID}Card`)) {
            existing.set(card.dataset.src || '', card);
        }

        const wanted = new Set();
        let added = 0;

        for (const image of state.filteredImages) {
            wanted.add(image.src);
            if (existing.has(image.src)) {
                continue;
            }

            const order = state.imageOrder.get(image.src) ?? 0;
            const card = createCardElement(image, order);
            const anchor = [...gallery.querySelectorAll(`.${ROOT_ID}Card`)]
                .find((node) => Number(node.dataset.order) > order);
            if (anchor) {
                gallery.insertBefore(card, anchor);
            } else {
                gallery.appendChild(card);
            }
            added += 1;
        }

        let removed = 0;
        for (const [src, card] of existing) {
            if (!wanted.has(src)) {
                card.remove();
                removed += 1;
            }
        }

        const empty = ensureEmptyNode(gallery);
        empty.hidden = state.filteredImages.length > 0;
        scheduleMasonryResize();
        return { added, removed };
    }

    function renderGallery() {
        const gallery = document.getElementById(`${ROOT_ID}Gallery`);
        if (!gallery) {
            return;
        }

        bindGalleryDelegates(gallery);
        syncGalleryCards(gallery);
    }

    function renderModal() {
        ensureModalShell();
        renderMetaTips();
        renderStats();
        renderFilterButtons();
        renderGallery();
        syncLoggingUi();
    }

    function syncLoggingUi() {
        const buttonText = state.loggingEnabled ? '日志已开启' : '开启日志';
        const buttonIds = [
            `${ROOT_ID}ToggleLog`,
            `${ROOT_ID}ToggleLogFromPanel`
        ];

        for (const id of buttonIds) {
            const button = document.getElementById(id);
            if (!button) {
                continue;
            }
            button.textContent = buttonText;
            button.classList.toggle('success', state.loggingEnabled);
        }
    }

    function refreshLogViewer() {
        const logList = document.getElementById(`${ROOT_ID}LogList`);
        if (!logList) {
            return;
        }

        if (state.logs.length === 0) {
            logList.innerHTML = '暂无日志。建议先开启日志，再复现问题后复制给我。';
            return;
        }

        logList.innerHTML = state.logs
            .map((entry) => `<div class="${ROOT_ID}LogLine ${escapeHtml(entry.level)}">${escapeHtml(formatLogEntry(entry))}</div>`)
            .join('');
    }

    function openLogViewer() {
        state.showLogViewer = true;
        let modal = document.getElementById(`${ROOT_ID}LogModal`);
        if (!modal) {
            injectPanelCss();
            modal = document.createElement('div');
            modal.id = `${ROOT_ID}LogModal`;
            modal.setAttribute(UI_MARK_ATTR, '1');
            modal.innerHTML = `
                <div id="${ROOT_ID}LogPanel">
                    <div id="${ROOT_ID}LogHeader">
                        <div>
                            <h2>运行日志</h2>
                            <p>这里会记录用户操作、扫描结果、下载状态、异常信息。复现问题后可直接点击“复制日志”发给我。</p>
                        </div>
                        <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}CloseLog">关闭</button>
                    </div>
                    <div id="${ROOT_ID}LogToolbar">
                        <button type="button" class="${ROOT_ID}Btn ${state.loggingEnabled ? 'success' : ''}" id="${ROOT_ID}ToggleLogFromPanel">${state.loggingEnabled ? '日志已开启' : '开启日志'}</button>
                        <button type="button" class="${ROOT_ID}Btn primary" id="${ROOT_ID}CopyLog">复制日志</button>
                        <button type="button" class="${ROOT_ID}Btn" id="${ROOT_ID}ClearLog">清空日志</button>
                    </div>
                    <div id="${ROOT_ID}LogList"></div>
                </div>
            `;
            modal.addEventListener('click', (event) => {
                if (event.target === modal) {
                    closeLogViewer();
                }
            });
            modal.querySelector(`#${ROOT_ID}CloseLog`).addEventListener('click', closeLogViewer);
            modal.querySelector(`#${ROOT_ID}ToggleLogFromPanel`).addEventListener('click', toggleLoggingEnabled);
            modal.querySelector(`#${ROOT_ID}CopyLog`).addEventListener('click', copyLogsToClipboard);
            modal.querySelector(`#${ROOT_ID}ClearLog`).addEventListener('click', clearLogs);
            document.body.appendChild(modal);
        }
        syncLoggingUi();
        refreshLogViewer();
        addLog('debug', '用户打开日志面板');
    }

    function toggleLoggingEnabled() {
        state.loggingEnabled = !state.loggingEnabled;
        storeBoolean(STORAGE_KEYS.loggingEnabled, state.loggingEnabled);
        addLog('info', `日志记录已${state.loggingEnabled ? '开启' : '关闭'}`);
        syncLoggingUi();
        renderModal();
        refreshLogViewer();
    }

    function getSelectedImagesInOrder() {
        return state.allImages.filter((image) => state.selectedImages.has(image.src));
    }

    function parseStartIndex() {
        const input = document.getElementById(`${ROOT_ID}StartIndex`);
        const value = Number.parseInt(input?.value || '1', 10);
        return Number.isFinite(value) && value > 0 ? value : 1;
    }

    function getDownloadButton() {
        return document.getElementById(`${ROOT_ID}Download`);
    }

    function setDownloadProgress(text, disabled) {
        const button = getDownloadButton();
        if (!button) {
            return;
        }
        button.textContent = text;
        button.disabled = disabled;
    }

    function startDownload(options) {
        return new Promise((resolve, reject) => {
            const downloadOptions = {
                ...options,
                saveAs: false,
                conflictAction: 'overwrite',
                onload: resolve,
                onerror: reject,
                ontimeout: reject
            };

            try {
                GM_download(downloadOptions);
            } catch (error) {
                const fallbackOptions = { ...downloadOptions };
                delete fallbackOptions.conflictAction;
                try {
                    GM_download(fallbackOptions);
                } catch (fallbackError) {
                    reject(fallbackError);
                }
            }
        });
    }

    async function downloadSelectedImages() {
        if (state.isDownloading) {
            return;
        }

        const imagesToDownload = getSelectedImagesInOrder();
        if (imagesToDownload.length === 0) {
            notify('请先选中要下载的图片。');
            return;
        }

        const meta = getPageMeta();
        const downloadHint = getDownloadModeHint();
        addLog('info', '准备下载图片', {
            count: imagesToDownload.length,
            folderPath: meta.folderPath,
            mode: downloadHint.mode,
            hint: downloadHint.subfolderHint
        });

        state.isDownloading = true;
        const startIndex = parseStartIndex();
        let successCount = 0;
        let failCount = 0;

        setDownloadProgress(`准备下载 0/${imagesToDownload.length}`, true);

        try {
            for (let i = 0; i < imagesToDownload.length; i += 1) {
                const image = imagesToDownload[i];
                const serial = String(startIndex + i).padStart(3, '0');
                const downloadPath = buildDownloadPath(image, serial);

                setDownloadProgress(`下载中 ${i + 1}/${imagesToDownload.length}`, true);
                addLog('debug', '开始下载单张图片', {
                    index: i + 1,
                    total: imagesToDownload.length,
                    path: downloadPath,
                    src: image.src
                });

                try {
                    await startDownload({
                        url: image.src,
                        name: downloadPath,
                        timeout: 60000
                    });
                    successCount += 1;
                    addLog('debug', '下载成功', { path: downloadPath });
                } catch (error) {
                    failCount += 1;
                    addLog('error', '下载失败', {
                        path: downloadPath,
                        src: image.src,
                        error: String(error?.error || error?.message || error)
                    });
                }

                if (state.downloadDelay > 0 && i < imagesToDownload.length - 1) {
                    await sleep(state.downloadDelay);
                }
            }

            notify(`下载完成：成功 ${successCount} 张，失败 ${failCount} 张。文件夹：${meta.folderPath}`);
            addLog('info', '下载任务结束', {
                successCount,
                failCount,
                folderPath: meta.folderPath
            });
        } finally {
            state.isDownloading = false;
            setDownloadProgress('下载选中图片', false);
        }
    }

    function clampNumber(value, min, max) {
        return Math.min(Math.max(value, min), max);
    }

    function getFloatingDefaultY(button) {
        const buttonHeight = button.offsetHeight || 52;
        return clampNumber(
            window.innerHeight - buttonHeight - FLOATING_BUTTON_BOTTOM,
            FLOATING_BUTTON_MARGIN,
            Math.max(FLOATING_BUTTON_MARGIN, window.innerHeight - buttonHeight - FLOATING_BUTTON_MARGIN)
        );
    }

    function clampFloatingY(button, y) {
        const buttonHeight = button.offsetHeight || 52;
        return clampNumber(
            y,
            FLOATING_BUTTON_MARGIN,
            Math.max(FLOATING_BUTTON_MARGIN, window.innerHeight - buttonHeight - FLOATING_BUTTON_MARGIN)
        );
    }

    function applyFloatingButtonPosition(button) {
        const position = state.floatingButtonPosition || { edge: 'right', y: null };
        const y = clampFloatingY(
            button,
            Number.isFinite(Number(position.y)) ? Number(position.y) : getFloatingDefaultY(button)
        );

        state.floatingButtonPosition = {
            edge: position.edge === 'left' ? 'left' : 'right',
            y
        };

        button.style.top = `${y}px`;
        button.style.bottom = 'auto';
        if (state.floatingButtonPosition.edge === 'left') {
            button.style.left = `${FLOATING_DOCK_OFFSET}px`;
            button.style.right = 'auto';
            button.dataset.edge = 'left';
        } else {
            button.style.left = 'auto';
            button.style.right = `${FLOATING_DOCK_OFFSET}px`;
            button.dataset.edge = 'right';
        }
    }

    function storeFloatingButtonPosition() {
        storeValue(STORAGE_KEYS.floatingPosition, state.floatingButtonPosition);
    }

    function enablePlugin() {
        state.pluginEnabled = true;
        storeBoolean(STORAGE_KEYS.pluginEnabled, true);
        createFloatingButton();
        notify('图片提取工具悬浮按钮已启用。');
        addLog('info', '用户通过菜单启用悬浮按钮');
    }

    function scrollPageToBottom() {
        const scrollingElement = document.scrollingElement || document.documentElement;
        const maxScrollTop = scrollingElement.scrollHeight - scrollingElement.clientHeight;
        if (maxScrollTop > 0) {
            scrollingElement.scrollTop = maxScrollTop;
        }
        addLog('info', '用户右键悬浮按钮，页面已滚动到最底部');
    }

    function createFloatingButton() {
        if (!state.pluginEnabled) {
            return;
        }

        if (document.getElementById(`${ROOT_ID}FloatingButton`)) {
            return;
        }

        const button = document.createElement('button');
        button.id = `${ROOT_ID}FloatingButton`;
        button.setAttribute(UI_MARK_ATTR, '1');
        button.type = 'button';
        button.setAttribute('aria-label', '打开图片提取器');
        button.innerHTML = `
            <span class="${ROOT_ID}FloatingIcon" aria-hidden="true">
                <svg viewBox="0 0 28 28" fill="none" xmlns="http://www.w3.org/2000/svg">
                    <rect x="4.75" y="5.5" width="16.5" height="14.5" rx="3.25" stroke="currentColor" stroke-width="2"/>
                    <path d="M7.8 17.65L11.15 14.05C11.68 13.48 12.57 13.45 13.14 13.98L15.05 15.75L16.03 14.72C16.56 14.16 17.44 14.13 18.01 14.65L21.05 17.45" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
                    <circle cx="16.9" cy="10.25" r="1.45" fill="currentColor"/>
                    <path d="M19.25 21.25H23.25C23.8 21.25 24.25 20.8 24.25 20.25V16.25" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>
                    <path d="M24 20.9L18.6 15.5" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>
                </svg>
            </span>
        `;
        button.title = '点击打开图片提取器；拖动可调整位置并自动吸附边缘；右键直达页面最底部';
        let dragState = null;
        let ignoreNextClick = false;

        button.addEventListener('pointerdown', (event) => {
            if (event.button !== 0) {
                return;
            }

            const rect = button.getBoundingClientRect();
            dragState = {
                pointerId: event.pointerId,
                startX: event.clientX,
                startY: event.clientY,
                initialLeft: rect.left,
                initialTop: rect.top,
                moved: false
            };
            button.setPointerCapture?.(event.pointerId);
        });

        button.addEventListener('pointermove', (event) => {
            if (!dragState || event.pointerId !== dragState.pointerId) {
                return;
            }

            const deltaX = event.clientX - dragState.startX;
            const deltaY = event.clientY - dragState.startY;
            if (!dragState.moved && Math.hypot(deltaX, deltaY) < FLOATING_DRAG_THRESHOLD) {
                return;
            }

            dragState.moved = true;
            const width = button.offsetWidth || 52;
            const nextLeft = clampNumber(
                dragState.initialLeft + deltaX,
                FLOATING_BUTTON_MARGIN,
                Math.max(FLOATING_BUTTON_MARGIN, window.innerWidth - width - FLOATING_BUTTON_MARGIN)
            );
            const nextTop = clampFloatingY(button, dragState.initialTop + deltaY);

            button.classList.add('dragging');
            button.style.left = `${nextLeft}px`;
            button.style.right = 'auto';
            button.style.top = `${nextTop}px`;
            button.style.bottom = 'auto';
            event.preventDefault();
        });

        function finishDrag(event) {
            if (!dragState || event.pointerId !== dragState.pointerId) {
                return;
            }

            button.releasePointerCapture?.(event.pointerId);
            const wasMoved = dragState.moved;
            dragState = null;
            button.classList.remove('dragging');

            if (!wasMoved) {
                return;
            }

            const rect = button.getBoundingClientRect();
            state.floatingButtonPosition = {
                edge: rect.left + rect.width / 2 < window.innerWidth / 2 ? 'left' : 'right',
                y: clampFloatingY(button, rect.top)
            };
            applyFloatingButtonPosition(button);
            storeFloatingButtonPosition();
            ignoreNextClick = true;
            window.setTimeout(() => {
                ignoreNextClick = false;
            }, 80);
            addLog('info', '用户拖动悬浮按钮并吸附边缘', state.floatingButtonPosition);
        }

        button.addEventListener('pointerup', finishDrag);
        button.addEventListener('pointercancel', finishDrag);
        button.addEventListener('click', () => {
            if (ignoreNextClick) {
                return;
            }
            addLog('info', '用户点击悬浮按钮启动');
            collectAllImages();
        });
        button.addEventListener('contextmenu', (event) => {
            event.preventDefault();
            scrollPageToBottom();
        });
        document.body.appendChild(button);
        applyFloatingButtonPosition(button);
    }

    function registerMenu() {
        if (typeof GM_registerMenuCommand !== 'function') {
            return;
        }
        GM_registerMenuCommand('启动图片提取工具', () => {
            if (!state.pluginEnabled) {
                enablePlugin();
            }
            collectAllImages();
        });
        GM_registerMenuCommand('启用/显示悬浮按钮', enablePlugin);
        GM_registerMenuCommand(state.loggingEnabled ? '关闭日志记录' : '开启日志记录', toggleLoggingEnabled);
        GM_registerMenuCommand('查看运行日志', openLogViewer);
    }

    function registerGlobalErrorHooks() {
        window.addEventListener('error', (event) => {
            addLog('error', '捕获到运行时错误', {
                message: event.message,
                file: event.filename,
                line: event.lineno,
                column: event.colno
            });
        });

        window.addEventListener('unhandledrejection', (event) => {
            addLog('error', '捕获到未处理的 Promise 异常', {
                reason: String(event.reason?.message || event.reason || 'unknown')
            });
        });
    }

    function registerFloatingButtonResizeHandler() {
        window.addEventListener('resize', () => {
            const button = document.getElementById(`${ROOT_ID}FloatingButton`);
            if (button) {
                applyFloatingButtonPosition(button);
                storeFloatingButtonPosition();
            }
            scheduleMasonryResize();
        });
    }

    function init() {
        registerMenu();
        registerGlobalErrorHooks();
        registerFloatingButtonResizeHandler();
        initXiaohongshuLinkEnhancer();
        createFloatingButton();
        addLog('info', '脚本初始化完成', {
            version: VERSION,
            pluginEnabled: state.pluginEnabled,
            url: window.location.href,
            userAgent: navigator.userAgent,
            scriptHandler: GM_info?.scriptHandler || 'unknown'
        });
    }

    if (document.readyState === 'loading') {
        window.addEventListener('DOMContentLoaded', init, { once: true });
    } else {
        init();
    }
})();
