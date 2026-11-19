(function () {
  'use strict';

  const Engine = window.LuffarschackEngine;
  if (!Engine) {
    throw new Error('LuffarschackEngine failed to load.');
  }

  const { EMPTY, PLAYER_X, PLAYER_O, DIFFICULTY_LEVELS, opponentOf, checkWinAt, findBestMove } = Engine;

  const COL_LETTERS = 'ABCDEFGHIJKLMNOPQRSTUVWXY';

  // DOM References
  const elHtml = document.documentElement;
  const elThemeToggle = document.getElementById('theme-toggle');
  const elThemeLabel = document.getElementById('theme-label');
  const elHeaderStatusDot = document.getElementById('header-status-dot');
  const elHeaderStatusText = document.getElementById('header-status-text');

  const elSpecGrid = document.getElementById('spec-grid');
  const elMoveCount = document.getElementById('move-count');
  const elLastCoord = document.getElementById('last-coord');

  const elBoardViewport = document.getElementById('board-viewport');
  const elBoardStage = document.getElementById('board-stage');
  const elCoordsTop = document.getElementById('coords-top');
  const elCoordsLeft = document.getElementById('coords-left');
  const elBoardGrid = document.getElementById('board-grid');
  const elWinOverlay = document.getElementById('win-overlay');

  const elConfirmBar = document.getElementById('confirm-bar');
  const elConfirmTag = document.getElementById('confirm-tag');
  const elConfirmText = document.getElementById('confirm-text');
  const elConfirmCancel = document.getElementById('confirm-cancel');
  const elConfirmPlace = document.getElementById('confirm-place');

  const elZoomOut = document.getElementById('zoom-out');
  const elZoomReset = document.getElementById('zoom-reset');
  const elZoomIn = document.getElementById('zoom-in');

  const elTurnGlyph = document.getElementById('turn-glyph');
  const elStatusHeadline = document.getElementById('status-headline');
  const elStatusSubline = document.getElementById('status-subline');
  const elEngineMs = document.getElementById('engine-ms');
  const elEngineDepth = document.getElementById('engine-depth');

  const elBtnUndo = document.getElementById('btn-undo');
  const elBtnReset = document.getElementById('btn-reset');
  const elGridSelector = document.getElementById('grid-selector');
  const elDiffSelector = document.getElementById('difficulty-selector');
  const elSideSelector = document.getElementById('side-selector');
  const elConfirmTapToggle = document.getElementById('confirm-tap-toggle');
  const elInspectToggle = document.getElementById('inspect-engine-toggle');

  const elInspectorPanel = document.getElementById('inspector-panel');
  const elInspectorModeBadge = document.getElementById('inspector-mode-badge');
  const elInspectorCoord = document.getElementById('inspector-coord');
  const elInspectorSummary = document.getElementById('inspector-summary');
  const elInspectorTime = document.getElementById('inspector-time');
  const elInspectorDepth = document.getElementById('inspector-depth');
  const elInspectorNodes = document.getElementById('inspector-nodes');
  const elInspectorTT = document.getElementById('inspector-tt');
  const elInspectorCandidates = document.getElementById('inspector-candidates');

  const elScoreHuman = document.getElementById('score-human');
  const elScoreAi = document.getElementById('score-ai');
  const elScoreDraw = document.getElementById('score-draw');

  // Application State
  const mobileMedia = window.matchMedia('(max-width: 768px)');
  const coarseMedia = window.matchMedia('(pointer: coarse)');

  const state = {
    size: 19,
    board: new Uint8Array(19 * 19),
    history: [], // { index, player }
    humanPlayer: PLAYER_X,
    level: 3, // 1..5 (default 3 · Tactical)
    currentTurn: PLAYER_X,
    gameOver: false,
    winInfo: null,
    isDraw: false,
    scoredOutcome: null,
    aiThinking: false,
    aiTimerId: null,
    activeRequestId: 0,
    stagedIdx: -1,
    confirmTap: mobileMedia.matches || coarseMedia.matches,
    confirmTapUserOverride: false,
    inspectEngine: false,
    inspectorData: null,
    lastEngineStats: null,
    scores: { human: 0, ai: 0, draw: 0 },
  };

  // Non-blocking Web Worker (with seamless main-thread fallback if blocked under file://)
  let engineWorker = null;
  let workerAvailable = false;
  const pendingCallbacks = new Map();

  function initEngineWorker() {
    if (typeof Worker === 'undefined') return;
    try {
      const worker = new Worker('engine.js');
      worker.onmessage = (event) => {
        const msg = event.data;
        if (!msg || !msg.requestId) return;
        const cb = pendingCallbacks.get(msg.requestId);
        if (!cb) return;
        pendingCallbacks.delete(msg.requestId);
        if (msg.type === 'BEST_MOVE_RESULT') {
          cb(null, msg.result, msg.purpose);
        } else {
          cb(new Error(msg.error || 'Engine worker error'), null, msg.purpose);
        }
      };
      worker.onerror = () => {
        // Silently degrade to main-thread fallback if Worker script fails to load
        workerAvailable = false;
        engineWorker = null;
        const pending = Array.from(pendingCallbacks.entries());
        pendingCallbacks.clear();
        for (let i = 0; i < pending.length; i++) {
          pending[i][1](new Error('worker-fallback'), null, 'move');
        }
      };
      engineWorker = worker;
      workerAvailable = true;
    } catch (_) {
      workerAvailable = false;
      engineWorker = null;
    }
  }

  function runEngineSearch(boardSnapshot, size, player, level, purpose, callback) {
    state.activeRequestId += 1;
    const reqId = state.activeRequestId;

    if (workerAvailable && engineWorker) {
      pendingCallbacks.set(reqId, (err, result) => {
        if (reqId !== state.activeRequestId) return;
        if (err && err.message === 'worker-fallback') {
          const fallbackRes = findBestMove(boardSnapshot, size, player, level);
          callback(fallbackRes);
          return;
        }
        callback(result);
      });
      engineWorker.postMessage({
        type: 'FIND_BEST_MOVE',
        requestId: reqId,
        purpose,
        board: boardSnapshot,
        size,
        player,
        level,
      });
      return reqId;
    }

    // Fallback non-blocking timer tick (e.g., file:// protocol)
    state.aiTimerId = window.setTimeout(() => {
      state.aiTimerId = null;
      if (reqId !== state.activeRequestId) return;
      const result = findBestMove(boardSnapshot, size, player, level);
      callback(result);
    }, 24);
    return reqId;
  }

  function cancelPendingSearches() {
    state.activeRequestId += 1;
    pendingCallbacks.clear();
    if (state.aiTimerId !== null) {
      window.clearTimeout(state.aiTimerId);
      state.aiTimerId = null;
    }
    state.aiThinking = false;
  }

  // Cached grid element arrays & Inspector cell overlay map
  let cellEls = [];
  let topCoordEls = [];
  let leftCoordEls = [];
  let activeHighlightRow = -1;
  let activeHighlightCol = -1;
  let evalOverlayMap = new Map(); // idx -> candidate obj

  // Zoom & Pan State
  const zoom = {
    scale: 1,
    tx: 0,
    ty: 0,
    min: 1,
    max: 3,
    pointers: new Map(),
    isPanning: false,
    isPinching: false,
    dragStartX: 0,
    dragStartY: 0,
    startTx: 0,
    startTy: 0,
    pinchStartDist: 0,
    pinchStartScale: 1,
    pinchAnchorX: 0,
    pinchAnchorY: 0,
    suppressNextClick: false,
  };

  // =========================================================================
  // Helpers
  // =========================================================================

  function getAiPlayer() {
    return opponentOf(state.humanPlayer);
  }

  function getLevelConfig() {
    return DIFFICULTY_LEVELS[state.level] || DIFFICULTY_LEVELS[3];
  }

  function playerSymbol(player) {
    return player === PLAYER_X ? 'X' : 'O';
  }

  function formatCoord(idx) {
    if (idx < 0 || idx >= state.size * state.size) return '—';
    const r = (idx / state.size) | 0;
    const c = idx - r * state.size;
    return `${COL_LETTERS[c]}${r + 1}`;
  }

  function createMarkMarkup(player, isGhost) {
    const ghostClass = isGhost ? ' is-ghost' : '';
    if (player === PLAYER_X) {
      return (
        `<svg class="mark-svg is-x${ghostClass}" viewBox="0 0 24 24" fill="none" stroke-width="2.9" stroke-linecap="square" aria-hidden="true">` +
        `<path d="M5.2 5.2L18.8 18.8M18.8 5.2L5.2 18.8"/>` +
        `</svg>`
      );
    }
    return (
      `<svg class="mark-svg is-o${ghostClass}" viewBox="0 0 24 24" fill="none" stroke-width="2.7" aria-hidden="true">` +
      `<circle cx="12" cy="12" r="7.2"/>` +
      `</svg>`
    );
  }

  // =========================================================================
  // Theme Handling
  // =========================================================================

  function applyTheme(theme) {
    const next = theme === 'dark' ? 'dark' : 'light';
    elHtml.setAttribute('data-theme', next);
    elThemeLabel.textContent = next === 'dark' ? 'Light' : 'Dark';
    try {
      window.localStorage.setItem('luffarschack-theme', next);
    } catch (_) {
      // Ignore storage restrictions
    }
  }

  function initTheme() {
    let saved = 'light';
    try {
      const stored = window.localStorage.getItem('luffarschack-theme');
      if (stored === 'dark' || stored === 'light') {
        saved = stored;
      }
    } catch (_) {
      // Default light
    }
    applyTheme(saved);
  }

  function toggleTheme() {
    const current = elHtml.getAttribute('data-theme');
    applyTheme(current === 'dark' ? 'light' : 'dark');
  }

  // =========================================================================
  // Board & Inspector Overlay Rendering
  // =========================================================================

  function buildBoardDOM() {
    const n = state.size;
    elBoardStage.style.setProperty('--grid-size', String(n));
    elBoardStage.setAttribute('data-size', String(n));
    elBoardGrid.setAttribute('aria-label', `Luffarschack ${n} by ${n} board`);
    elSpecGrid.textContent = `${n} × ${n}`;

    const topFrag = document.createDocumentFragment();
    topCoordEls = new Array(n);
    for (let c = 0; c < n; c++) {
      const span = document.createElement('span');
      span.className = 'coord-label';
      span.textContent = COL_LETTERS[c];
      topCoordEls[c] = span;
      topFrag.appendChild(span);
    }
    elCoordsTop.replaceChildren(topFrag);

    const leftFrag = document.createDocumentFragment();
    leftCoordEls = new Array(n);
    for (let r = 0; r < n; r++) {
      const span = document.createElement('span');
      span.className = 'coord-label';
      span.textContent = String(r + 1);
      leftCoordEls[r] = span;
      leftFrag.appendChild(span);
    }
    elCoordsLeft.replaceChildren(leftFrag);

    const gridFrag = document.createDocumentFragment();
    const total = n * n;
    const center = (n / 2) | 0;
    const centerIdx = center * n + center;
    cellEls = new Array(total);

    for (let idx = 0; idx < total; idx++) {
      const r = (idx / n) | 0;
      const c = idx - r * n;
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = idx === centerIdx ? 'cell is-center' : 'cell';
      btn.dataset.idx = String(idx);
      btn.setAttribute('role', 'gridcell');
      btn.setAttribute('aria-label', `${COL_LETTERS[c]}${r + 1}, empty`);
      cellEls[idx] = btn;
      gridFrag.appendChild(btn);
    }
    elBoardGrid.replaceChildren(gridFrag);

    elWinOverlay.setAttribute('viewBox', `0 0 ${n * 100} ${n * 100}`);
    elWinOverlay.replaceChildren();

    activeHighlightRow = -1;
    activeHighlightCol = -1;
    evalOverlayMap.clear();
    resetZoom();
  }

  function highlightCoords(row, col) {
    if (activeHighlightRow === row && activeHighlightCol === col) return;

    if (activeHighlightRow >= 0 && leftCoordEls[activeHighlightRow]) {
      leftCoordEls[activeHighlightRow].classList.remove('is-highlight');
    }
    if (activeHighlightCol >= 0 && topCoordEls[activeHighlightCol]) {
      topCoordEls[activeHighlightCol].classList.remove('is-highlight');
    }

    activeHighlightRow = row;
    activeHighlightCol = col;

    if (row >= 0 && leftCoordEls[row]) {
      leftCoordEls[row].classList.add('is-highlight');
    }
    if (col >= 0 && topCoordEls[col]) {
      topCoordEls[col].classList.add('is-highlight');
    }
  }

  function rebuildEvalOverlayMap() {
    const prevIndices = Array.from(evalOverlayMap.keys());
    evalOverlayMap.clear();

    if (state.inspectEngine && state.inspectorData && Array.isArray(state.inspectorData.topCandidates)) {
      const list = state.inspectorData.topCandidates;
      for (let i = 0; i < list.length && i < 8; i++) {
        const item = list[i];
        if (item.index >= 0 && item.index < state.size * state.size) {
          evalOverlayMap.set(item.index, item);
        }
      }
    }

    const dirty = new Set(prevIndices);
    evalOverlayMap.forEach((_, idx) => dirty.add(idx));
    dirty.forEach((idx) => updateCellVisual(idx));
  }

  function updateCellVisual(idx) {
    const el = cellEls[idx];
    if (!el) return;
    const n = state.size;
    const r = (idx / n) | 0;
    const c = idx - r * n;
    const val = state.board[idx];
    const center = (n / 2) | 0;
    const isCenter = r === center && c === center;
    const lastIdx = state.history.length > 0 ? state.history[state.history.length - 1].index : -1;
    const isWinCell = Boolean(state.winInfo && state.winInfo.line.includes(idx));
    const isStaged = state.stagedIdx === idx && val === EMPTY;
    const evalInfo = state.inspectEngine ? evalOverlayMap.get(idx) : null;

    const classes = ['cell'];
    if (isCenter) classes.push('is-center');

    let markMarkup = '';
    let markKey = '';

    if (val !== EMPTY) {
      classes.push('is-occupied', val === PLAYER_X ? 'has-x' : 'has-o');
      if (idx === lastIdx) classes.push('is-last');
      if (isWinCell) classes.push('is-win');
      markMarkup = createMarkMarkup(val, false);
      markKey = `m${val}`;
      el.setAttribute('aria-label', `${COL_LETTERS[c]}${r + 1}, ${playerSymbol(val)}`);
    } else if (isStaged) {
      classes.push('is-staged');
      markMarkup = createMarkMarkup(state.humanPlayer, true);
      markKey = `g${state.humanPlayer}`;
      el.setAttribute('aria-label', `${COL_LETTERS[c]}${r + 1}, staged ${playerSymbol(state.humanPlayer)}`);
    } else {
      el.setAttribute('aria-label', `${COL_LETTERS[c]}${r + 1}, empty`);
    }

    let evalMarkup = '';
    let evalKey = '';
    if (evalInfo && !isStaged) {
      if (val === EMPTY) {
        classes.push('has-eval');
        if (evalInfo.rank === 1 || evalInfo.isChosen) classes.push('has-eval-best');
        evalMarkup = `<span class="cell-eval" aria-hidden="true">${evalInfo.displayScore}</span>`;
        evalKey = `e:${evalInfo.displayScore}:${evalInfo.rank}`;
      } else if (evalInfo.isChosen) {
        classes.push('has-eval-best');
        evalMarkup = `<span class="cell-eval" aria-hidden="true">${evalInfo.displayScore}</span>`;
        evalKey = `ec:${evalInfo.displayScore}`;
      }
    }

    el.className = classes.join(' ');
    const combinedKey = `${markKey}|${evalKey}`;
    if (el.dataset.renderKey !== combinedKey) {
      el.innerHTML = markMarkup + evalMarkup;
      el.dataset.renderKey = combinedKey;
    }
  }

  function renderWinLine() {
    elWinOverlay.replaceChildren();
    if (!state.winInfo || !state.winInfo.line || state.winInfo.line.length < 2) return;

    const n = state.size;
    const line = state.winInfo.line;
    const first = line[0];
    const last = line[line.length - 1];

    const r1 = (first / n) | 0;
    const c1 = first - r1 * n;
    const r2 = (last / n) | 0;
    const c2 = last - r2 * n;

    const cx1 = c1 * 100 + 50;
    const cy1 = r1 * 100 + 50;
    const cx2 = c2 * 100 + 50;
    const cy2 = r2 * 100 + 50;

    const dx = cx2 - cx1;
    const dy = cy2 - cy1;
    const dist = Math.hypot(dx, dy) || 1;
    const ux = dx / dist;
    const uy = dy / dist;
    const pad = 26;

    const x1 = cx1 - ux * pad;
    const y1 = cy1 - uy * pad;
    const x2 = cx2 + ux * pad;
    const y2 = cy2 + uy * pad;
    const totalLen = Math.hypot(x2 - x1, y2 - y1);

    const svgNS = 'http://www.w3.org/2000/svg';

    const halo = document.createElementNS(svgNS, 'line');
    halo.setAttribute('class', 'win-line-halo');
    halo.setAttribute('x1', String(x1));
    halo.setAttribute('y1', String(y1));
    halo.setAttribute('x2', String(x2));
    halo.setAttribute('y2', String(y2));
    halo.setAttribute('stroke-width', '24');

    const main = document.createElementNS(svgNS, 'line');
    main.setAttribute('class', 'win-line-main');
    main.setAttribute('x1', String(x1));
    main.setAttribute('y1', String(y1));
    main.setAttribute('x2', String(x2));
    main.setAttribute('y2', String(y2));
    main.setAttribute('stroke-width', '13');
    main.style.strokeDasharray = String(totalLen);
    main.style.strokeDashoffset = String(totalLen);

    elWinOverlay.appendChild(halo);
    elWinOverlay.appendChild(main);

    window.requestAnimationFrame(() => {
      window.requestAnimationFrame(() => {
        main.style.strokeDashoffset = '0';
      });
    });
  }

  function syncAllCells() {
    const total = state.size * state.size;
    for (let i = 0; i < total; i++) {
      updateCellVisual(i);
    }
  }

  function updateInspectorPanel() {
    elInspectToggle.setAttribute('aria-checked', String(state.inspectEngine));
    elInspectorPanel.hidden = !state.inspectEngine;
    if (!state.inspectEngine) return;

    const data = state.inspectorData;
    if (!data) {
      elInspectorModeBadge.textContent = state.aiThinking ? 'SEARCHING' : 'READY';
      elInspectorModeBadge.classList.remove('is-vcf');
      elInspectorCoord.textContent = '—';
      elInspectorSummary.textContent = state.aiThinking
        ? 'Evaluating candidate threat lines…'
        : 'Place a move to inspect JEV evaluations.';
      elInspectorTime.textContent = '—';
      elInspectorDepth.textContent = '—';
      elInspectorNodes.textContent = '—';
      elInspectorTT.textContent = '—';
      elInspectorCandidates.replaceChildren();
      return;
    }

    const isVcfEvent = Boolean(data.vcfWinPlies || data.vcfBlockedPlies);
    elInspectorModeBadge.classList.toggle('is-vcf', isVcfEvent);
    if (data.vcfWinPlies) {
      elInspectorModeBadge.textContent = `VCF · ${data.vcfWinPlies}P`;
    } else if (data.vcfBlockedPlies) {
      elInspectorModeBadge.textContent = `VCF DEF`;
    } else {
      elInspectorModeBadge.textContent = `L${data.level} · JEV`;
    }

    elInspectorCoord.textContent = formatCoord(data.chosenIndex);
    elInspectorSummary.textContent = data.summary || 'Positional evaluation';
    elInspectorTime.textContent = `${data.durationMs.toFixed(1)} ms`;
    elInspectorDepth.textContent = data.vcfWinPlies ? `VCF ${data.vcfWinPlies}p` : `D${data.depth}`;
    elInspectorNodes.textContent = data.nodes.toLocaleString();
    elInspectorTT.textContent = data.ttHits ? data.ttHits.toLocaleString() : '0';

    const frag = document.createDocumentFragment();
    const list = data.topCandidates || [];
    for (let i = 0; i < list.length && i < 8; i++) {
      const c = list[i];
      const chip = document.createElement('div');
      chip.className = c.isChosen ? 'cand-chip is-chosen' : 'cand-chip';
      chip.title = `${formatCoord(c.index)}: ${c.summary} (${c.score})`;
      chip.innerHTML =
        `<span class="cand-coord">#${c.rank} ${formatCoord(c.index)}</span>` +
        `<span class="cand-score">${c.displayScore}</span>`;
      frag.appendChild(chip);
    }
    elInspectorCandidates.replaceChildren(frag);
  }

  function updateUI() {
    const moveCount = state.history.length;
    const lastMove = moveCount > 0 ? state.history[moveCount - 1] : null;
    const aiPlayer = getAiPlayer();
    const lvl = getLevelConfig();
    const isHumanTurn = !state.gameOver && !state.aiThinking && state.currentTurn === state.humanPlayer;

    elBoardGrid.classList.toggle('turn-x', state.humanPlayer === PLAYER_X);
    elBoardGrid.classList.toggle('turn-o', state.humanPlayer === PLAYER_O);
    elBoardGrid.classList.toggle('is-locked', !isHumanTurn);

    elMoveCount.textContent = String(moveCount).padStart(2, '0');
    elLastCoord.textContent = lastMove ? `${playerSymbol(lastMove.player)}·${formatCoord(lastMove.index)}` : '—';

    if (state.lastEngineStats) {
      elEngineMs.textContent = `${state.lastEngineStats.durationMs.toFixed(1)} ms`;
      elEngineDepth.textContent = state.lastEngineStats.vcfPlies
        ? `VCF ${state.lastEngineStats.vcfPlies}p`
        : `D${state.lastEngineStats.depth}`;
    } else {
      elEngineMs.textContent = '—';
      elEngineDepth.textContent = '—';
    }

    elHeaderStatusDot.className = 'status-dot';
    elTurnGlyph.className = 'turn-glyph';

    if (state.winInfo) {
      const humanWon = state.winInfo.winner === state.humanPlayer;
      const winSym = playerSymbol(state.winInfo.winner);
      elTurnGlyph.textContent = winSym;
      if (state.winInfo.winner === PLAYER_O) elTurnGlyph.classList.add('is-o');
      elHeaderStatusDot.classList.add('is-win');

      if (humanWon) {
        elStatusHeadline.textContent = `Victory — ${winSym}`;
        elStatusSubline.textContent = `Five in a row achieved in ${moveCount} moves.`;
        elHeaderStatusText.textContent = `YOU WIN · ${winSym}`;
      } else {
        elStatusHeadline.textContent = `Engine Wins — ${winSym}`;
        elStatusSubline.textContent = `Five in a row completed at ${formatCoord(lastMove.index)}.`;
        elHeaderStatusText.textContent = `ENGINE WINS · ${winSym}`;
      }
    } else if (state.isDraw) {
      elTurnGlyph.textContent = '—';
      elStatusHeadline.textContent = 'Draw';
      elStatusSubline.textContent = 'Board full with no five-in-a-row.';
      elHeaderStatusText.textContent = 'DRAW GAME';
    } else if (state.aiThinking || state.currentTurn === aiPlayer) {
      const aiSym = playerSymbol(aiPlayer);
      elTurnGlyph.textContent = aiSym;
      if (aiPlayer === PLAYER_O) {
        elTurnGlyph.classList.add('is-o');
        elHeaderStatusDot.classList.add('is-o');
      }
      elStatusHeadline.textContent = 'Engine Thinking…';
      elStatusSubline.textContent = `Level ${lvl.id} · ${lvl.name} (${lvl.shortSpec})`;
      elHeaderStatusText.textContent = `ENGINE · ${aiSym}`;
    } else {
      const huSym = playerSymbol(state.humanPlayer);
      elTurnGlyph.textContent = huSym;
      if (state.humanPlayer === PLAYER_O) {
        elTurnGlyph.classList.add('is-o');
        elHeaderStatusDot.classList.add('is-o');
      }
      elStatusHeadline.textContent = 'Your Turn';
      elStatusSubline.textContent =
        moveCount === 0
          ? `Place ${huSym} to open · Level ${lvl.id} ${lvl.name}`
          : `Playing ${huSym} vs L${lvl.id} · ${lvl.name}`;
      elHeaderStatusText.textContent = `YOUR TURN · ${huSym}`;
    }

    const humanHasMoved = state.history.some((m) => m.player === state.humanPlayer);
    elBtnUndo.disabled = !humanHasMoved;

    elConfirmTapToggle.setAttribute('aria-checked', String(state.confirmTap));
    const showConfirmBar = state.confirmTap && !state.gameOver;
    elConfirmBar.classList.toggle('is-visible', showConfirmBar);
    const hasStaged = state.stagedIdx >= 0 && state.board[state.stagedIdx] === EMPTY && isHumanTurn;
    elConfirmBar.classList.toggle('has-staged', hasStaged);

    if (hasStaged) {
      elConfirmTag.textContent = `STAGED ${playerSymbol(state.humanPlayer)}`;
      elConfirmText.textContent = `Cell ${formatCoord(state.stagedIdx)}`;
      elConfirmCancel.disabled = false;
      elConfirmPlace.disabled = false;
    } else {
      elConfirmTag.textContent = 'AIM MODE';
      elConfirmText.textContent = isHumanTurn ? 'Tap cell to aim' : 'Engine thinking…';
      elConfirmCancel.disabled = true;
      elConfirmPlace.disabled = true;
    }

    elScoreHuman.textContent = String(state.scores.human);
    elScoreAi.textContent = String(state.scores.ai);
    elScoreDraw.textContent = String(state.scores.draw);

    updateInspectorPanel();
  }

  // =========================================================================
  // Game Flow & Non-Blocking Worker Search
  // =========================================================================

  function setStagedCell(idx) {
    const prev = state.stagedIdx;
    if (prev === idx) return;
    state.stagedIdx = idx;
    if (prev >= 0) updateCellVisual(prev);
    if (idx >= 0) {
      updateCellVisual(idx);
      const r = (idx / state.size) | 0;
      const c = idx - r * state.size;
      highlightCoords(r, c);
    } else {
      highlightCoords(-1, -1);
    }
    updateUI();
  }

  function commitMove(idx, player) {
    if (state.gameOver || idx < 0 || idx >= state.board.length || state.board[idx] !== EMPTY) {
      return false;
    }

    const prevLastIdx = state.history.length > 0 ? state.history[state.history.length - 1].index : -1;

    if (state.stagedIdx >= 0) {
      const oldStaged = state.stagedIdx;
      state.stagedIdx = -1;
      if (oldStaged !== idx) updateCellVisual(oldStaged);
    }

    state.board[idx] = player;
    state.history.push({ index: idx, player });

    if (prevLastIdx >= 0) updateCellVisual(prevLastIdx);
    updateCellVisual(idx);

    const win = checkWinAt(state.board, state.size, idx);
    if (win) {
      state.gameOver = true;
      state.winInfo = win;
      for (let i = 0; i < win.line.length; i++) {
        updateCellVisual(win.line[i]);
      }
      renderWinLine();
      if (win.winner === state.humanPlayer) {
        state.scores.human += 1;
        state.scoredOutcome = 'human';
      } else {
        state.scores.ai += 1;
        state.scoredOutcome = 'ai';
      }
      updateUI();
      return true;
    }

    if (state.history.length >= state.size * state.size) {
      state.gameOver = true;
      state.isDraw = true;
      state.scores.draw += 1;
      state.scoredOutcome = 'draw';
      updateUI();
      return true;
    }

    state.currentTurn = opponentOf(player);
    updateUI();
    return true;
  }

  function scheduleAiMove() {
    if (state.gameOver || state.currentTurn !== getAiPlayer()) return;
    cancelPendingSearches();
    state.aiThinking = true;
    updateUI();

    const aiPlayer = getAiPlayer();
    const snapshot = new Uint8Array(state.board);

    runEngineSearch(snapshot, state.size, aiPlayer, state.level, 'move', (result) => {
      state.aiThinking = false;
      if (state.gameOver || state.currentTurn !== aiPlayer) {
        updateUI();
        return;
      }

      if (result) {
        state.lastEngineStats = {
          durationMs: result.durationMs,
          depth: result.depth,
          vcfPlies: result.inspector ? result.inspector.vcfWinPlies : null,
        };
        state.inspectorData = result.inspector || null;
        commitMove(result.index, aiPlayer);
        rebuildEvalOverlayMap();
        updateInspectorPanel();
      } else {
        updateUI();
      }
    });
  }

  function triggerLiveInspectSnapshot() {
    if (!state.inspectEngine || state.aiThinking || state.gameOver) return;
    const snapshot = new Uint8Array(state.board);
    const sideToAnalyze = state.currentTurn;

    runEngineSearch(snapshot, state.size, sideToAnalyze, state.level, 'inspect', (result) => {
      if (!state.inspectEngine || state.aiThinking) return;
      if (result && result.inspector) {
        state.inspectorData = result.inspector;
        rebuildEvalOverlayMap();
        updateInspectorPanel();
      }
    });
  }

  function handleCellInteraction(idx) {
    if (state.gameOver || state.aiThinking || state.currentTurn !== state.humanPlayer) {
      return;
    }
    if (state.board[idx] !== EMPTY) {
      return;
    }

    if (state.confirmTap) {
      if (state.stagedIdx === idx) {
        const placed = commitMove(idx, state.humanPlayer);
        if (placed && !state.gameOver) {
          scheduleAiMove();
        }
      } else {
        setStagedCell(idx);
      }
    } else {
      const placed = commitMove(idx, state.humanPlayer);
      if (placed && !state.gameOver) {
        scheduleAiMove();
      }
    }
  }

  function confirmStagedMove() {
    if (state.stagedIdx < 0 || state.gameOver || state.aiThinking || state.currentTurn !== state.humanPlayer) {
      return;
    }
    const target = state.stagedIdx;
    const placed = commitMove(target, state.humanPlayer);
    if (placed && !state.gameOver) {
      scheduleAiMove();
    }
  }

  function undoMove() {
    const humanHasMoved = state.history.some((m) => m.player === state.humanPlayer);
    if (!humanHasMoved) return;

    cancelPendingSearches();
    setStagedCell(-1);

    if (state.scoredOutcome) {
      state.scores[state.scoredOutcome] = Math.max(0, state.scores[state.scoredOutcome] - 1);
      state.scoredOutcome = null;
    }

    const oldWinLine = state.winInfo ? state.winInfo.line.slice() : [];
    state.gameOver = false;
    state.winInfo = null;
    state.isDraw = false;
    state.inspectorData = null;
    elWinOverlay.replaceChildren();

    const poppedIndices = [];
    while (state.history.length > 0) {
      const last = state.history.pop();
      state.board[last.index] = EMPTY;
      poppedIndices.push(last.index);
      if (last.player === state.humanPlayer) {
        break;
      }
    }

    state.currentTurn = state.humanPlayer;

    for (let i = 0; i < oldWinLine.length; i++) updateCellVisual(oldWinLine[i]);
    for (let i = 0; i < poppedIndices.length; i++) updateCellVisual(poppedIndices[i]);
    if (state.history.length > 0) {
      updateCellVisual(state.history[state.history.length - 1].index);
    }

    rebuildEvalOverlayMap();
    updateUI();

    if (state.inspectEngine && state.history.length > 0) {
      triggerLiveInspectSnapshot();
    }
  }

  function resetGame(rebuildGrid) {
    cancelPendingSearches();
    state.board = new Uint8Array(state.size * state.size);
    state.history = [];
    state.currentTurn = PLAYER_X;
    state.gameOver = false;
    state.winInfo = null;
    state.isDraw = false;
    state.scoredOutcome = null;
    state.stagedIdx = -1;
    state.lastEngineStats = null;
    state.inspectorData = null;

    if (rebuildGrid) {
      buildBoardDOM();
    } else {
      elWinOverlay.replaceChildren();
      evalOverlayMap.clear();
      syncAllCells();
      highlightCoords(-1, -1);
    }

    updateUI();

    if (state.humanPlayer === PLAYER_O) {
      scheduleAiMove();
    } else if (state.inspectEngine) {
      triggerLiveInspectSnapshot();
    }
  }

  // =========================================================================
  // Zoom, Pan & Pinch-Zoom Engine
  // =========================================================================

  function clampTransform(scale, tx, ty) {
    const rect = elBoardViewport.getBoundingClientRect();
    const minTx = Math.min(0, rect.width * (1 - scale));
    const minTy = Math.min(0, rect.height * (1 - scale));
    return {
      tx: Math.max(minTx, Math.min(0, tx)),
      ty: Math.max(minTy, Math.min(0, ty)),
    };
  }

  function applyZoomTransform() {
    elBoardStage.style.transform = `translate3d(${zoom.tx.toFixed(2)}px, ${zoom.ty.toFixed(2)}px, 0) scale(${zoom.scale.toFixed(4)})`;
    elZoomReset.textContent = `${Math.round(zoom.scale * 100)}%`;
    elBoardViewport.classList.toggle('is-zoomed', zoom.scale > 1.01);
    elBoardViewport.classList.toggle('is-panning', zoom.isPanning);
  }

  function setZoomCentered(targetScale, focalX, focalY) {
    const rect = elBoardViewport.getBoundingClientRect();
    const newScale = Math.max(zoom.min, Math.min(zoom.max, targetScale));
    const fx = typeof focalX === 'number' ? focalX : rect.width * 0.5;
    const fy = typeof focalY === 'number' ? focalY : rect.height * 0.5;

    const stageX = (fx - zoom.tx) / zoom.scale;
    const stageY = (fy - zoom.ty) / zoom.scale;

    const rawTx = fx - stageX * newScale;
    const rawTy = fy - stageY * newScale;
    const clamped = clampTransform(newScale, rawTx, rawTy);

    zoom.scale = newScale;
    zoom.tx = clamped.tx;
    zoom.ty = clamped.ty;
    applyZoomTransform();
  }

  function resetZoom() {
    zoom.scale = 1;
    zoom.tx = 0;
    zoom.ty = 0;
    zoom.isPanning = false;
    zoom.isPinching = false;
    applyZoomTransform();
  }

  function initZoomGestures() {
    elZoomIn.addEventListener('click', () => setZoomCentered(zoom.scale + 0.4));
    elZoomOut.addEventListener('click', () => setZoomCentered(zoom.scale - 0.4));
    elZoomReset.addEventListener('click', resetZoom);

    elBoardViewport.addEventListener(
      'wheel',
      (e) => {
        if (!e.ctrlKey) return;
        e.preventDefault();
        const rect = elBoardViewport.getBoundingClientRect();
        const fx = e.clientX - rect.left;
        const fy = e.clientY - rect.top;
        const delta = e.deltaY < 0 ? 0.25 : -0.25;
        setZoomCentered(zoom.scale + delta, fx, fy);
      },
      { passive: false }
    );

    elBoardViewport.addEventListener('pointerdown', (e) => {
      if (e.pointerType === 'mouse' && e.button !== 0) return;
      zoom.pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });

      if (zoom.pointers.size === 2) {
        const pts = Array.from(zoom.pointers.values());
        const rect = elBoardViewport.getBoundingClientRect();
        zoom.isPinching = true;
        zoom.isPanning = false;
        zoom.suppressNextClick = true;
        zoom.pinchStartDist = Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y) || 1;
        zoom.pinchStartScale = zoom.scale;
        const midX = (pts[0].x + pts[1].x) * 0.5 - rect.left;
        const midY = (pts[0].y + pts[1].y) * 0.5 - rect.top;
        zoom.pinchAnchorX = (midX - zoom.tx) / zoom.scale;
        zoom.pinchAnchorY = (midY - zoom.ty) / zoom.scale;
      } else if (zoom.pointers.size === 1) {
        zoom.dragStartX = e.clientX;
        zoom.dragStartY = e.clientY;
        zoom.startTx = zoom.tx;
        zoom.startTy = zoom.ty;
        zoom.isPanning = false;
      }
    });

    elBoardViewport.addEventListener('pointermove', (e) => {
      if (!zoom.pointers.has(e.pointerId)) return;
      zoom.pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });

      if (zoom.pointers.size === 2 && zoom.isPinching) {
        const pts = Array.from(zoom.pointers.values());
        const rect = elBoardViewport.getBoundingClientRect();
        const dist = Math.hypot(pts[1].x - pts[0].x, pts[1].y - pts[0].y);
        const newScale = Math.max(zoom.min, Math.min(zoom.max, zoom.pinchStartScale * (dist / zoom.pinchStartDist)));
        const midX = (pts[0].x + pts[1].x) * 0.5 - rect.left;
        const midY = (pts[0].y + pts[1].y) * 0.5 - rect.top;

        const rawTx = midX - zoom.pinchAnchorX * newScale;
        const rawTy = midY - zoom.pinchAnchorY * newScale;
        const clamped = clampTransform(newScale, rawTx, rawTy);

        zoom.scale = newScale;
        zoom.tx = clamped.tx;
        zoom.ty = clamped.ty;
        applyZoomTransform();
      } else if (zoom.pointers.size === 1 && zoom.scale > 1.01 && !zoom.isPinching) {
        const dx = e.clientX - zoom.dragStartX;
        const dy = e.clientY - zoom.dragStartY;
        if (!zoom.isPanning && Math.hypot(dx, dy) > 7) {
          zoom.isPanning = true;
          zoom.suppressNextClick = true;
        }
        if (zoom.isPanning) {
          const clamped = clampTransform(zoom.scale, zoom.startTx + dx, zoom.startTy + dy);
          zoom.tx = clamped.tx;
          zoom.ty = clamped.ty;
          applyZoomTransform();
        }
      }
    });

    function handlePointerEnd(e) {
      zoom.pointers.delete(e.pointerId);
      if (zoom.pointers.size < 2) {
        zoom.isPinching = false;
      }
      if (zoom.pointers.size === 0) {
        if (zoom.isPanning) {
          zoom.isPanning = false;
          applyZoomTransform();
        }
        if (zoom.suppressNextClick) {
          window.setTimeout(() => {
            zoom.suppressNextClick = false;
          }, 50);
        }
      } else if (zoom.pointers.size === 1) {
        const rem = Array.from(zoom.pointers.values())[0];
        zoom.dragStartX = rem.x;
        zoom.dragStartY = rem.y;
        zoom.startTx = zoom.tx;
        zoom.startTy = zoom.ty;
      }
    }

    elBoardViewport.addEventListener('pointerup', handlePointerEnd);
    elBoardViewport.addEventListener('pointercancel', handlePointerEnd);
    elBoardViewport.addEventListener('pointerleave', (e) => {
      if (e.pointerType === 'mouse') {
        handlePointerEnd(e);
      }
    });

    window.addEventListener('resize', () => {
      if (zoom.scale > 1) {
        const clamped = clampTransform(zoom.scale, zoom.tx, zoom.ty);
        zoom.tx = clamped.tx;
        zoom.ty = clamped.ty;
        applyZoomTransform();
      }
    });
  }

  // =========================================================================
  // Event Binding
  // =========================================================================

  function setActiveRadio(container, selector, attr, value) {
    const buttons = container.querySelectorAll(selector);
    buttons.forEach((btn) => {
      const match = btn.getAttribute(attr) === String(value);
      btn.classList.toggle('is-active', match);
      btn.setAttribute('aria-checked', String(match));
    });
  }

  function bindEvents() {
    elThemeToggle.addEventListener('click', toggleTheme);

    elBoardGrid.addEventListener('click', (e) => {
      if (zoom.suppressNextClick) {
        zoom.suppressNextClick = false;
        return;
      }
      const cell = e.target.closest('.cell');
      if (!cell) return;
      const idx = Number(cell.dataset.idx);
      if (Number.isInteger(idx)) {
        handleCellInteraction(idx);
      }
    });

    elBoardGrid.addEventListener('pointerover', (e) => {
      if (e.pointerType === 'touch') return;
      const cell = e.target.closest('.cell');
      if (!cell) return;
      const idx = Number(cell.dataset.idx);
      if (Number.isInteger(idx)) {
        const r = (idx / state.size) | 0;
        const c = idx - r * state.size;
        highlightCoords(r, c);
      }
    });

    elBoardGrid.addEventListener('pointerleave', () => {
      if (state.stagedIdx >= 0) {
        const r = (state.stagedIdx / state.size) | 0;
        const c = state.stagedIdx - r * state.size;
        highlightCoords(r, c);
      } else {
        highlightCoords(-1, -1);
      }
    });

    elConfirmPlace.addEventListener('click', confirmStagedMove);
    elConfirmCancel.addEventListener('click', () => setStagedCell(-1));

    elBtnUndo.addEventListener('click', undoMove);
    elBtnReset.addEventListener('click', () => resetGame(false));

    // Grid size selector
    elGridSelector.addEventListener('click', (e) => {
      const btn = e.target.closest('.seg-btn');
      if (!btn) return;
      const nextSize = Number(btn.getAttribute('data-size'));
      if (![15, 19, 25].includes(nextSize) || nextSize === state.size) return;
      state.size = nextSize;
      setActiveRadio(elGridSelector, '.seg-btn', 'data-size', nextSize);
      resetGame(true);
    });

    // Five-tier difficulty selector
    elDiffSelector.addEventListener('click', (e) => {
      const btn = e.target.closest('.level-btn');
      if (!btn) return;
      const nextLevel = Number(btn.getAttribute('data-level'));
      if (!DIFFICULTY_LEVELS[nextLevel] || nextLevel === state.level) return;
      state.level = nextLevel;
      setActiveRadio(elDiffSelector, '.level-btn', 'data-level', nextLevel);
      updateUI();
      if (state.inspectEngine && !state.aiThinking && !state.gameOver && state.history.length > 0) {
        triggerLiveInspectSnapshot();
      }
    });

    // Side selector
    elSideSelector.addEventListener('click', (e) => {
      const btn = e.target.closest('.seg-btn');
      if (!btn) return;
      const nextSide = Number(btn.getAttribute('data-side'));
      if ((nextSide !== PLAYER_X && nextSide !== PLAYER_O) || nextSide === state.humanPlayer) return;
      state.humanPlayer = nextSide;
      setActiveRadio(elSideSelector, '.seg-btn', 'data-side', nextSide);
      resetGame(false);
    });

    // Inspect Engine switch
    elInspectToggle.addEventListener('click', () => {
      state.inspectEngine = !state.inspectEngine;
      rebuildEvalOverlayMap();
      updateUI();
      if (state.inspectEngine && !state.inspectorData && !state.aiThinking && !state.gameOver) {
        triggerLiveInspectSnapshot();
      }
    });

    // Confirm tap switch
    elConfirmTapToggle.addEventListener('click', () => {
      state.confirmTapUserOverride = true;
      state.confirmTap = !state.confirmTap;
      if (!state.confirmTap && state.stagedIdx >= 0) {
        setStagedCell(-1);
      } else {
        updateUI();
      }
    });

    const onViewportChange = () => {
      if (state.confirmTapUserOverride) return;
      const shouldConfirm = mobileMedia.matches || coarseMedia.matches;
      if (state.confirmTap !== shouldConfirm) {
        state.confirmTap = shouldConfirm;
        if (!state.confirmTap && state.stagedIdx >= 0) {
          setStagedCell(-1);
        } else {
          updateUI();
        }
      }
    };

    if (typeof mobileMedia.addEventListener === 'function') {
      mobileMedia.addEventListener('change', onViewportChange);
    }

    // Keyboard shortcuts
    window.addEventListener('keydown', (e) => {
      if (e.target && (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA')) return;

      if (e.key === 'Escape' && state.stagedIdx >= 0) {
        e.preventDefault();
        setStagedCell(-1);
        return;
      }

      if (e.key === 'Enter' && state.stagedIdx >= 0 && state.confirmTap) {
        e.preventDefault();
        confirmStagedMove();
        return;
      }

      if ((e.key === 'z' || e.key === 'Z') && !e.altKey) {
        if (e.ctrlKey || e.metaKey || !e.shiftKey) {
          if (!elBtnUndo.disabled) {
            e.preventDefault();
            undoMove();
          }
        }
        return;
      }

      if ((e.key === 'r' || e.key === 'R') && !e.ctrlKey && !e.metaKey && !e.altKey) {
        e.preventDefault();
        resetGame(false);
        return;
      }

      if ((e.key === 't' || e.key === 'T') && !e.ctrlKey && !e.metaKey && !e.altKey) {
        e.preventDefault();
        toggleTheme();
        return;
      }

      if ((e.key === 'i' || e.key === 'I') && !e.ctrlKey && !e.metaKey && !e.altKey) {
        e.preventDefault();
        elInspectToggle.click();
      }
    });
  }

  // =========================================================================
  // Initialization
  // =========================================================================

  initEngineWorker();
  initTheme();
  buildBoardDOM();
  initZoomGestures();
  bindEvents();
  updateUI();
})();
