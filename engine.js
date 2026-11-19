(function (globalScope) {
  'use strict';

  const EMPTY = 0;
  const PLAYER_X = 1;
  const PLAYER_O = 2;

  const DIRS = [
    [0, 1],  // Horizontal
    [1, 0],  // Vertical
    [1, 1],  // Diagonal down-right
    [1, -1], // Diagonal down-left
  ];

  // Explicit JEV Weighted Threat Matrix across all 4 axes
  const THREAT_WEIGHTS = {
    WINNING_FIVE: 1000000,
    OPEN_FOUR: 120000,
    DOUBLE_THREAT: 65000,
    CLOSED_FOUR: 18000,
    OPEN_THREE: 9500,
    BROKEN_OPEN_THREE: 5500,
    CLOSED_THREE: 900,
    OPEN_TWO: 350,
    CLOSED_TWO: 75,
    ONE: 15,
  };

  // Five distinct difficulty levels
  const DIFFICULTY_LEVELS = {
    1: {
      id: 1,
      key: 'casual',
      name: 'Casual',
      shortSpec: 'D1 · ~1 ms',
      maxDepth: 1,
      rootBranch: 10,
      innerBranch: 6,
      timeBudgetMs: 4,
      useTT: false,
      useVCF: false,
      vcfPlies: 0,
    },
    2: {
      id: 2,
      key: 'club',
      name: 'Club',
      shortSpec: 'D2 · ~5 ms',
      maxDepth: 2,
      rootBranch: 10,
      innerBranch: 7,
      timeBudgetMs: 12,
      useTT: false,
      useVCF: false,
      vcfPlies: 0,
    },
    3: {
      id: 3,
      key: 'tactical',
      name: 'Tactical',
      shortSpec: 'D4 · ~35 ms',
      maxDepth: 4,
      rootBranch: 12,
      innerBranch: 8,
      timeBudgetMs: 38,
      useTT: false,
      useVCF: false,
      vcfPlies: 0,
    },
    4: {
      id: 4,
      key: 'master',
      name: 'Master',
      shortSpec: 'D6 · Zobrist TT',
      maxDepth: 6,
      rootBranch: 14,
      innerBranch: 9,
      timeBudgetMs: 120,
      useTT: true,
      useVCF: false,
      vcfPlies: 0,
    },
    5: {
      id: 5,
      key: 'grandmaster',
      name: 'Grandmaster',
      shortSpec: 'D6 + VCF 14p',
      maxDepth: 6,
      rootBranch: 14,
      innerBranch: 9,
      timeBudgetMs: 250,
      useTT: true,
      useVCF: true,
      vcfPlies: 14,
    },
  };

  function resolveLevelConfig(levelOrKey) {
    if (typeof levelOrKey === 'number' && DIFFICULTY_LEVELS[levelOrKey]) {
      return DIFFICULTY_LEVELS[levelOrKey];
    }
    if (typeof levelOrKey === 'string') {
      const num = Number(levelOrKey);
      if (DIFFICULTY_LEVELS[num]) return DIFFICULTY_LEVELS[num];
      const lower = levelOrKey.toLowerCase();
      for (let k = 1; k <= 5; k++) {
        if (DIFFICULTY_LEVELS[k].key === lower) return DIFFICULTY_LEVELS[k];
      }
      if (lower === 'easy') return DIFFICULTY_LEVELS[1];
      if (lower === 'medium') return DIFFICULTY_LEVELS[2];
      if (lower === 'hard') return DIFFICULTY_LEVELS[3];
    }
    return DIFFICULTY_LEVELS[3];
  }

  function opponentOf(player) {
    return player === PLAYER_X ? PLAYER_O : PLAYER_X;
  }

  function nowMs() {
    return typeof performance !== 'undefined' ? performance.now() : Date.now();
  }

  // =========================================================================
  // Deterministic Zobrist Tables & Fixed-Size Transposition Table
  // =========================================================================

  const MAX_CELLS = 25 * 25;
  const ZOBRIST_HI = new Uint32Array(MAX_CELLS * 2);
  const ZOBRIST_LO = new Uint32Array(MAX_CELLS * 2);

  (function initZobrist() {
    let seed = 0x9e3779b9;
    function nextU32() {
      seed = (seed + 0x6d2b79f5) | 0;
      let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return (t ^ (t >>> 14)) >>> 0;
    }
    for (let i = 0; i < MAX_CELLS * 2; i++) {
      ZOBRIST_HI[i] = nextU32();
      ZOBRIST_LO[i] = nextU32();
    }
  })();

  const TT_BITS = 17;
  const TT_SIZE = 1 << TT_BITS; // 131,072 entries
  const TT_MASK = TT_SIZE - 1;
  const TT_EXACT = 1;
  const TT_LOWER = 2;
  const TT_UPPER = 3;

  const ttKeyHi = new Uint32Array(TT_SIZE);
  const ttKeyLo = new Uint32Array(TT_SIZE);
  const ttDepth = new Int8Array(TT_SIZE);
  const ttFlag = new Uint8Array(TT_SIZE);
  const ttScore = new Int32Array(TT_SIZE);
  const ttBestMove = new Int16Array(TT_SIZE);
  const ttGen = new Uint16Array(TT_SIZE);
  let currentTTGen = 0;

  function computeBoardHash(board) {
    let hi = 0;
    let lo = 0;
    for (let i = 0; i < board.length; i++) {
      const p = board[i];
      if (p !== EMPTY) {
        const zIdx = (i << 1) + (p - 1);
        hi = (hi ^ ZOBRIST_HI[zIdx]) >>> 0;
        lo = (lo ^ ZOBRIST_LO[zIdx]) >>> 0;
      }
    }
    return { hi, lo };
  }

  // =========================================================================
  // Win Detection
  // =========================================================================

  function checkWinAt(board, size, lastIdx) {
    if (lastIdx < 0 || lastIdx >= board.length) return null;
    const player = board[lastIdx];
    if (player === EMPTY) return null;

    const r0 = (lastIdx / size) | 0;
    const c0 = lastIdx - r0 * size;

    for (let d = 0; d < 4; d++) {
      const dr = DIRS[d][0];
      const dc = DIRS[d][1];

      let rStart = r0;
      let cStart = c0;
      while (
        rStart - dr >= 0 &&
        rStart - dr < size &&
        cStart - dc >= 0 &&
        cStart - dc < size &&
        board[(rStart - dr) * size + (cStart - dc)] === player
      ) {
        rStart -= dr;
        cStart -= dc;
      }

      const line = [];
      let r = rStart;
      let c = cStart;
      while (r >= 0 && r < size && c >= 0 && c < size && board[r * size + c] === player) {
        line.push(r * size + c);
        r += dr;
        c += dc;
      }

      if (line.length >= 5) {
        return { winner: player, line };
      }
    }
    return null;
  }

  function checkWinBoard(board, size) {
    for (let r = 0; r < size; r++) {
      for (let c = 0; c < size; c++) {
        const idx = r * size + c;
        const player = board[idx];
        if (player === EMPTY) continue;
        for (let d = 0; d < 4; d++) {
          const dr = DIRS[d][0];
          const dc = DIRS[d][1];
          const prevR = r - dr;
          const prevC = c - dc;
          if (
            prevR >= 0 &&
            prevR < size &&
            prevC >= 0 &&
            prevC < size &&
            board[prevR * size + prevC] === player
          ) {
            continue;
          }
          let count = 1;
          let nr = r + dr;
          let nc = c + dc;
          while (nr >= 0 && nr < size && nc >= 0 && nc < size && board[nr * size + nc] === player) {
            count++;
            nr += dr;
            nc += dc;
          }
          if (count >= 5) {
            const line = [];
            for (let k = 0; k < count; k++) {
              line.push((r + dr * k) * size + (c + dc * k));
            }
            return { winner: player, line };
          }
        }
      }
    }
    return null;
  }

  // =========================================================================
  // JEV Weighted Threat Point Analyzer (Zero-Allocation Fast Path + Detailed)
  // =========================================================================

  function analyzePoint(board, size, r, c, player) {
    const opp = opponentOf(player);

    let fives = 0;
    let openFours = 0;
    let closedFours = 0;
    let openThrees = 0;
    let brokenOpenThrees = 0;
    let closedThrees = 0;
    let openTwos = 0;
    let closedTwos = 0;
    let ones = 0;

    for (let d = 0; d < 4; d++) {
      const dr = DIRS[d][0];
      const dc = DIRS[d][1];

      // Negative direction scan
      let lRun1 = 0;
      let lOpen1 = false;
      let lRun2 = 0;
      let lOpen2 = false;
      let lSpace = 0;

      let nr = r - dr;
      let nc = c - dc;
      while (nr >= 0 && nr < size && nc >= 0 && nc < size && lRun1 < 5) {
        const v = board[nr * size + nc];
        if (v === player) {
          lRun1++;
          lSpace++;
          nr -= dr;
          nc -= dc;
        } else {
          if (v === EMPTY) {
            lOpen1 = true;
            lSpace++;
            let nr2 = nr - dr;
            let nc2 = nc - dc;
            while (nr2 >= 0 && nr2 < size && nc2 >= 0 && nc2 < size && lRun2 < 4) {
              const v2 = board[nr2 * size + nc2];
              if (v2 === player) {
                lRun2++;
                lSpace++;
                nr2 -= dr;
                nc2 -= dc;
              } else {
                if (v2 === EMPTY) {
                  lOpen2 = true;
                  lSpace++;
                }
                break;
              }
            }
            let nr3 = nr2;
            let nc3 = nc2;
            if (lOpen2) {
              nr3 -= dr;
              nc3 -= dc;
            }
            while (
              lSpace < 4 &&
              nr3 >= 0 &&
              nr3 < size &&
              nc3 >= 0 &&
              nc3 < size &&
              board[nr3 * size + nc3] !== opp
            ) {
              lSpace++;
              nr3 -= dr;
              nc3 -= dc;
            }
          }
          break;
        }
      }

      // Positive direction scan
      let rRun1 = 0;
      let rOpen1 = false;
      let rRun2 = 0;
      let rOpen2 = false;
      let rSpace = 0;

      nr = r + dr;
      nc = c + dc;
      while (nr >= 0 && nr < size && nc >= 0 && nc < size && rRun1 < 5) {
        const v = board[nr * size + nc];
        if (v === player) {
          rRun1++;
          rSpace++;
          nr += dr;
          nc += dc;
        } else {
          if (v === EMPTY) {
            rOpen1 = true;
            rSpace++;
            let nr2 = nr + dr;
            let nc2 = nc + dc;
            while (nr2 >= 0 && nr2 < size && nc2 >= 0 && nc2 < size && rRun2 < 4) {
              const v2 = board[nr2 * size + nc2];
              if (v2 === player) {
                rRun2++;
                rSpace++;
                nr2 += dr;
                nc2 += dc;
              } else {
                if (v2 === EMPTY) {
                  rOpen2 = true;
                  rSpace++;
                }
                break;
              }
            }
            let nr3 = nr2;
            let nc3 = nc2;
            if (rOpen2) {
              nr3 += dr;
              nc3 += dc;
            }
            while (
              rSpace < 4 &&
              nr3 >= 0 &&
              nr3 < size &&
              nc3 >= 0 &&
              nc3 < size &&
              board[nr3 * size + nc3] !== opp
            ) {
              rSpace++;
              nr3 += dr;
              nc3 += dc;
            }
          }
          break;
        }
      }

      const totalRun = 1 + lRun1 + rRun1;
      const totalAvail = 1 + lSpace + rSpace;

      if (totalRun >= 5) {
        fives++;
        continue;
      }
      if (totalAvail < 5) {
        continue;
      }

      if (totalRun === 4) {
        if (lOpen1 && rOpen1) {
          openFours++;
        } else if (lOpen1 || rOpen1) {
          closedFours++;
        }
      } else if (totalRun === 3) {
        const leftSplit4 = lOpen1 && lRun2 >= 1;
        const rightSplit4 = rOpen1 && rRun2 >= 1;
        if (leftSplit4 && rightSplit4) {
          openFours++;
        } else if (leftSplit4 || rightSplit4) {
          closedFours++;
        } else if (lOpen1 && rOpen1) {
          openThrees++;
        } else if (lOpen1 || rOpen1) {
          closedThrees++;
        }
      } else if (totalRun === 2) {
        const leftSplit4 = lOpen1 && lRun2 >= 2;
        const rightSplit4 = rOpen1 && rRun2 >= 2;
        if (leftSplit4 && rightSplit4) {
          openFours++;
        } else if (leftSplit4 || rightSplit4) {
          closedFours++;
        } else {
          const leftSplit3 = lOpen1 && lRun2 === 1;
          const rightSplit3 = rOpen1 && rRun2 === 1;
          if ((leftSplit3 && lOpen2 && rOpen1) || (rightSplit3 && rOpen2 && lOpen1)) {
            brokenOpenThrees++;
          } else if (leftSplit3 || rightSplit3) {
            closedThrees++;
          } else if (lOpen1 && rOpen1) {
            openTwos++;
          } else if (lOpen1 || rOpen1) {
            closedTwos++;
          }
        }
      } else {
        // totalRun === 1
        const leftSplit4 = lOpen1 && lRun2 >= 3;
        const rightSplit4 = rOpen1 && rRun2 >= 3;
        if (leftSplit4 && rightSplit4) {
          openFours++;
        } else if (leftSplit4 || rightSplit4) {
          closedFours++;
        } else {
          const leftSplit3 = lOpen1 && lRun2 === 2;
          const rightSplit3 = rOpen1 && rRun2 === 2;
          if ((leftSplit3 && lOpen2 && rOpen1) || (rightSplit3 && rOpen2 && lOpen1)) {
            brokenOpenThrees++;
          } else if (leftSplit3 || rightSplit3) {
            closedThrees++;
          } else {
            const leftSplit2 = lOpen1 && lRun2 === 1;
            const rightSplit2 = rOpen1 && rRun2 === 1;
            if ((leftSplit2 && lOpen2 && rOpen1) || (rightSplit2 && rOpen2 && lOpen1)) {
              openTwos++;
            } else if (leftSplit2 || rightSplit2) {
              closedTwos++;
            } else if (lOpen1 && rOpen1) {
              ones++;
            }
          }
        }
      }
    }

    const liveThrees = openThrees + brokenOpenThrees;
    const isDoubleFour = closedFours >= 2;
    const isFourThree = closedFours >= 1 && liveThrees >= 1;
    const isDoubleThree = liveThrees >= 2;
    const isFork = isDoubleFour || isFourThree || isDoubleThree;

    let score = 0;
    if (fives > 0) {
      score = THREAT_WEIGHTS.WINNING_FIVE;
    } else if (openFours > 0) {
      score = THREAT_WEIGHTS.OPEN_FOUR + (openFours - 1) * 15000 + closedFours * THREAT_WEIGHTS.CLOSED_FOUR;
    } else if (isDoubleFour) {
      score = THREAT_WEIGHTS.OPEN_FOUR + THREAT_WEIGHTS.DOUBLE_THREAT * 0.25;
    } else {
      if (isFourThree || isDoubleThree) {
        score += THREAT_WEIGHTS.DOUBLE_THREAT;
      }
      score +=
        closedFours * THREAT_WEIGHTS.CLOSED_FOUR +
        openThrees * THREAT_WEIGHTS.OPEN_THREE +
        brokenOpenThrees * THREAT_WEIGHTS.BROKEN_OPEN_THREE +
        closedThrees * THREAT_WEIGHTS.CLOSED_THREE +
        openTwos * THREAT_WEIGHTS.OPEN_TWO +
        closedTwos * THREAT_WEIGHTS.CLOSED_TWO +
        ones * THREAT_WEIGHTS.ONE;
    }

    // Gentle center preference for cohesive opening play
    const mid = (size - 1) * 0.5;
    const dist = Math.abs(r - mid) + Math.abs(c - mid);
    score += Math.max(0, size - dist) * 1.5;

    return {
      score,
      fives,
      openFours,
      closedFours,
      openThrees,
      brokenOpenThrees,
      closedThrees,
      openTwos,
      closedTwos,
      ones,
      isDoubleFour,
      isFourThree,
      isDoubleThree,
      isFork,
    };
  }

  function evaluatePointScore(board, size, r, c, player) {
    return analyzePoint(board, size, r, c, player).score;
  }

  // =========================================================================
  // Full-Board JEV Static Evaluator (Active Bounding Box)
  // =========================================================================

  function evaluateBoard(board, size, aiPlayer, turnPlayer) {
    let minR = size;
    let maxR = -1;
    let minC = size;
    let maxC = -1;

    for (let r = 0; r < size; r++) {
      const rowOff = r * size;
      for (let c = 0; c < size; c++) {
        if (board[rowOff + c] !== EMPTY) {
          if (r < minR) minR = r;
          if (r > maxR) maxR = r;
          if (c < minC) minC = c;
          if (c > maxC) maxC = c;
        }
      }
    }

    if (maxR < 0) return 0;

    minR = Math.max(0, minR - 1);
    maxR = Math.min(size - 1, maxR + 1);
    minC = Math.max(0, minC - 1);
    maxC = Math.min(size - 1, maxC + 1);

    let aiOpen4 = 0;
    let aiClosed4 = 0;
    let aiOpen3 = 0;
    let aiBroken3 = 0;
    let aiScore = 0;

    let huOpen4 = 0;
    let huClosed4 = 0;
    let huOpen3 = 0;
    let huBroken3 = 0;
    let huScore = 0;

    for (let r = minR; r <= maxR; r++) {
      const rowOff = r * size;
      for (let c = minC; c <= maxC; c++) {
        const player = board[rowOff + c];
        if (player === EMPTY) continue;
        const opp = opponentOf(player);

        for (let d = 0; d < 4; d++) {
          const dr = DIRS[d][0];
          const dc = DIRS[d][1];
          const prevR = r - dr;
          const prevC = c - dc;

          if (
            prevR >= 0 &&
            prevR < size &&
            prevC >= 0 &&
            prevC < size &&
            board[prevR * size + prevC] === player
          ) {
            continue;
          }

          let len = 1;
          let nr = r + dr;
          let nc = c + dc;
          while (nr >= 0 && nr < size && nc >= 0 && nc < size && board[nr * size + nc] === player) {
            len++;
            nr += dr;
            nc += dc;
          }

          if (len >= 5) {
            return player === aiPlayer ? THREAT_WEIGHTS.WINNING_FIVE : -THREAT_WEIGHTS.WINNING_FIVE;
          }

          const openStart =
            prevR >= 0 &&
            prevR < size &&
            prevC >= 0 &&
            prevC < size &&
            board[prevR * size + prevC] === EMPTY;
          const openEnd =
            nr >= 0 &&
            nr < size &&
            nc >= 0 &&
            nc < size &&
            board[nr * size + nc] === EMPTY;

          if (!openStart && !openEnd) continue;

          // Forward gap-1 split extension
          let splitForward = 0;
          let splitForwardOpen = false;
          if (openEnd) {
            let sr = nr + dr;
            let sc = nc + dc;
            while (sr >= 0 && sr < size && sc >= 0 && sc < size && board[sr * size + sc] === player) {
              splitForward++;
              sr += dr;
              sc += dc;
            }
            if (
              splitForward > 0 &&
              sr >= 0 &&
              sr < size &&
              sc >= 0 &&
              sc < size &&
              board[sr * size + sc] === EMPTY
            ) {
              splitForwardOpen = true;
            }
          }

          let pts = 0;
          let isOpen4 = false;
          let isClosed4 = false;
          let isOpen3 = false;
          let isBroken3 = false;

          if (len === 4) {
            if (openStart && openEnd) {
              isOpen4 = true;
              pts = THREAT_WEIGHTS.OPEN_FOUR;
            } else {
              isClosed4 = true;
              pts = THREAT_WEIGHTS.CLOSED_FOUR;
            }
          } else if (len === 3) {
            if (splitForward >= 1) {
              isClosed4 = true;
              pts = THREAT_WEIGHTS.CLOSED_FOUR;
            } else if (openStart && openEnd) {
              const rB2 = prevR - dr;
              const cB2 = prevC - dc;
              const rA2 = nr + dr;
              const cA2 = nc + dc;
              const extBefore =
                rB2 >= 0 && rB2 < size && cB2 >= 0 && cB2 < size && board[rB2 * size + cB2] !== opp;
              const extAfter =
                rA2 >= 0 && rA2 < size && cA2 >= 0 && cA2 < size && board[rA2 * size + cA2] !== opp;
              if (extBefore || extAfter) {
                isOpen3 = true;
                pts = THREAT_WEIGHTS.OPEN_THREE;
              } else {
                pts = THREAT_WEIGHTS.CLOSED_THREE;
              }
            } else {
              pts = THREAT_WEIGHTS.CLOSED_THREE;
            }
          } else if (len === 2) {
            if (splitForward >= 2) {
              isClosed4 = true;
              pts = THREAT_WEIGHTS.CLOSED_FOUR;
            } else if (splitForward === 1) {
              if (openStart && splitForwardOpen) {
                isBroken3 = true;
                pts = THREAT_WEIGHTS.BROKEN_OPEN_THREE;
              } else {
                pts = THREAT_WEIGHTS.CLOSED_THREE;
              }
            } else if (openStart && openEnd) {
              pts = THREAT_WEIGHTS.OPEN_TWO;
            } else {
              pts = THREAT_WEIGHTS.CLOSED_TWO;
            }
          } else if (len === 1) {
            if (splitForward >= 3) {
              isClosed4 = true;
              pts = THREAT_WEIGHTS.CLOSED_FOUR;
            } else if (splitForward === 2) {
              if (openStart && splitForwardOpen) {
                isBroken3 = true;
                pts = THREAT_WEIGHTS.BROKEN_OPEN_THREE;
              } else {
                pts = THREAT_WEIGHTS.CLOSED_THREE * 0.85;
              }
            } else if (splitForward === 1 && openStart && splitForwardOpen) {
              pts = THREAT_WEIGHTS.OPEN_TWO * 0.75;
            } else if (openStart && openEnd) {
              pts = THREAT_WEIGHTS.ONE;
            }
          }

          if (player === aiPlayer) {
            aiScore += pts;
            if (isOpen4) aiOpen4++;
            if (isClosed4) aiClosed4++;
            if (isOpen3) aiOpen3++;
            if (isBroken3) aiBroken3++;
          } else {
            huScore += pts;
            if (isOpen4) huOpen4++;
            if (isClosed4) huClosed4++;
            if (isOpen3) huOpen3++;
            if (isBroken3) huBroken3++;
          }
        }
      }
    }

    const aiThrees = aiOpen3 + aiBroken3;
    const huThrees = huOpen3 + huBroken3;

    // Fork / multi-threat bonuses
    if (aiClosed4 >= 2 || (aiClosed4 >= 1 && aiThrees >= 1) || aiThrees >= 2) {
      aiScore += THREAT_WEIGHTS.DOUBLE_THREAT;
    }
    if (huClosed4 >= 2 || (huClosed4 >= 1 && huThrees >= 1) || huThrees >= 2) {
      huScore += THREAT_WEIGHTS.DOUBLE_THREAT;
    }

    // Tempo adjustments based on side to move
    if (turnPlayer === aiPlayer) {
      if (aiOpen4 > 0 || aiClosed4 > 0) return THREAT_WEIGHTS.WINNING_FIVE * 0.85;
      if (huOpen4 > 0 || huClosed4 >= 2) return -THREAT_WEIGHTS.WINNING_FIVE * 0.75;
      if (aiThrees > 0 && huClosed4 === 0) aiScore += THREAT_WEIGHTS.DOUBLE_THREAT * 0.85;
    } else {
      if (huOpen4 > 0 || huClosed4 > 0) return -THREAT_WEIGHTS.WINNING_FIVE * 0.85;
      if (aiOpen4 > 0 || aiClosed4 >= 2) return THREAT_WEIGHTS.WINNING_FIVE * 0.75;
      if (huThrees > 0 && aiClosed4 === 0) huScore += THREAT_WEIGHTS.DOUBLE_THREAT * 0.85;
    }

    return Math.round(aiScore - huScore * 1.1);
  }

  // =========================================================================
  // 2-Square Candidate Neighborhood Generation & Ordering
  // =========================================================================

  function collectNeighborhood(board, size, stampBuf, stampRef, radius) {
    const total = size * size;
    const rad = radius || 2;
    stampRef.id = (stampRef.id + 1) >>> 0;
    if (stampRef.id === 0) {
      stampBuf.fill(0);
      stampRef.id = 1;
    }
    const stamp = stampRef.id;
    const cells = [];

    for (let idx = 0; idx < total; idx++) {
      if (board[idx] === EMPTY) continue;
      const r = (idx / size) | 0;
      const c = idx - r * size;

      const rMin = r - rad < 0 ? 0 : r - rad;
      const rMax = r + rad >= size ? size - 1 : r + rad;
      const cMin = c - rad < 0 ? 0 : c - rad;
      const cMax = c + rad >= size ? size - 1 : c + rad;

      for (let nr = rMin; nr <= rMax; nr++) {
        const rowOff = nr * size;
        for (let nc = cMin; nc <= cMax; nc++) {
          const nIdx = rowOff + nc;
          if (board[nIdx] === EMPTY && stampBuf[nIdx] !== stamp) {
            stampBuf[nIdx] = stamp;
            cells.push(nIdx);
          }
        }
      }
    }
    return cells;
  }

  function generateCandidates(board, size, currentPlayer, branchLimit, stampBuf, stampRef, ttMoveIdx) {
    const opp = opponentOf(currentPlayer);
    const rawCandidates = collectNeighborhood(board, size, stampBuf, stampRef, 2);
    if (rawCandidates.length === 0) return [];

    const scored = [];
    let mustWinIdx = -1;
    const mustBlockList = [];
    const openFourAttacks = [];

    for (let i = 0; i < rawCandidates.length; i++) {
      const idx = rawCandidates[i];
      const r = (idx / size) | 0;
      const c = idx - r * size;

      const atkInfo = analyzePoint(board, size, r, c, currentPlayer);
      if (atkInfo.fives > 0) {
        mustWinIdx = idx;
        break;
      }

      const defInfo = analyzePoint(board, size, r, c, opp);
      if (defInfo.fives > 0) {
        mustBlockList.push({
          idx,
          score: atkInfo.score + defInfo.score * 2,
          atk: atkInfo.score,
          def: defInfo.score,
        });
      }
      if (atkInfo.openFours > 0 || atkInfo.isDoubleFour) {
        openFourAttacks.push({
          idx,
          score: atkInfo.score * 1.2 + defInfo.score,
          atk: atkInfo.score,
          def: defInfo.score,
        });
      }

      const ttBonus = idx === ttMoveIdx ? 500000 : 0;
      const combined = atkInfo.score * 1.06 + defInfo.score * 0.98 + ttBonus;
      scored.push({
        idx,
        score: combined,
        staticScore: atkInfo.score * 1.06 + defInfo.score * 0.98,
        atk: atkInfo.score,
        def: defInfo.score,
      });
    }

    if (mustWinIdx !== -1) {
      return [
        {
          idx: mustWinIdx,
          score: THREAT_WEIGHTS.WINNING_FIVE,
          staticScore: THREAT_WEIGHTS.WINNING_FIVE,
          atk: THREAT_WEIGHTS.WINNING_FIVE,
          def: 0,
          immediateWin: true,
        },
      ];
    }

    if (mustBlockList.length > 0) {
      mustBlockList.sort((a, b) => b.score - a.score);
      return mustBlockList;
    }

    if (openFourAttacks.length > 0) {
      openFourAttacks.sort((a, b) => b.score - a.score);
      return openFourAttacks.slice(0, Math.min(3, openFourAttacks.length));
    }

    scored.sort((a, b) => b.score - a.score);

    // If opponent threatens an Open Four or Fork, restrict search to urgent defensive/counter-four replies
    let maxDef = 0;
    for (let i = 0; i < Math.min(8, scored.length); i++) {
      if (scored[i].def > maxDef) maxDef = scored[i].def;
    }
    if (maxDef >= THREAT_WEIGHTS.DOUBLE_THREAT) {
      const urgent = scored.filter(
        (m) =>
          m.idx === ttMoveIdx ||
          m.def >= THREAT_WEIGHTS.BROKEN_OPEN_THREE ||
          m.atk >= THREAT_WEIGHTS.CLOSED_FOUR
      );
      if (urgent.length > 0) {
        return urgent.slice(0, Math.min(branchLimit, urgent.length));
      }
    }

    if (scored.length > branchLimit) {
      return scored.slice(0, branchLimit);
    }
    return scored;
  }

  // =========================================================================
  // Grandmaster VCF (Victory by Continuous Fours) Threat-Space Solver (14-ply)
  // =========================================================================

  /**
   * Assuming `board[moveIdx] === player`, find all empty squares within 4 cells
   * along any axis through `moveIdx` that immediately complete 5-in-a-row for `player`.
   * Stops early at 2 distinct winning squares (Open Four / Double Four = unstoppable).
   */
  function findWinningSquaresAfterMove(board, size, moveIdx, player) {
    const r0 = (moveIdx / size) | 0;
    const c0 = moveIdx - r0 * size;
    const wins = [];

    for (let d = 0; d < 4; d++) {
      const dr = DIRS[d][0];
      const dc = DIRS[d][1];
      for (let step = -4; step <= 4; step++) {
        if (step === 0) continue;
        const nr = r0 + dr * step;
        const nc = c0 + dc * step;
        if (nr < 0 || nr >= size || nc < 0 || nc >= size) continue;
        const eIdx = nr * size + nc;
        if (board[eIdx] !== EMPTY) continue;

        board[eIdx] = player;
        const isWin = checkWinAt(board, size, eIdx) !== null;
        board[eIdx] = EMPTY;

        if (isWin && wins.indexOf(eIdx) === -1) {
          wins.push(eIdx);
          if (wins.length >= 2) return wins;
        }
      }
    }
    return wins;
  }

  /**
   * Recursive VCF solver up to `maxPlies` (e.g., 14 plies = 7 continuous fours).
   * Returns `{ move, plies, sequence }` if a forced win exists, or `null`.
   */
  function solveVCF(board, size, attacker, maxPlies, hashHi, hashLo, ctx) {
    if (maxPlies <= 0) return null;
    ctx.nodes++;
    if ((ctx.nodes & 31) === 0 && nowMs() >= ctx.deadline) {
      ctx.timedOut = true;
      return null;
    }

    const cacheKey = hashHi * 4294967296 + hashLo;
    const prevFailedDepth = ctx.failedCache.get(cacheKey);
    if (prevFailedDepth !== undefined && prevFailedDepth >= maxPlies) {
      return null;
    }

    const defender = opponentOf(attacker);
    const candidates = collectNeighborhood(board, size, ctx.stampBuf, ctx.stampRef, 2);

    let defenderImmediateWin = false;
    const fourMoves = [];

    for (let i = 0; i < candidates.length; i++) {
      const idx = candidates[i];
      const r = (idx / size) | 0;
      const c = idx - r * size;

      const atk = analyzePoint(board, size, r, c, attacker);
      if (atk.fives > 0) {
        return { move: idx, plies: 1, sequence: [idx] };
      }

      if (!defenderImmediateWin) {
        const def = analyzePoint(board, size, r, c, defender);
        if (def.fives > 0) {
          defenderImmediateWin = true;
        }
      }

      if (atk.openFours > 0 || atk.closedFours > 0) {
        const priority =
          atk.openFours * 100000 +
          (atk.isDoubleFour ? 90000 : 0) +
          (atk.isFourThree ? 75000 : 0) +
          atk.closedFours * 18000 +
          atk.openThrees * 9500 +
          atk.brokenOpenThrees * 5500;
        fourMoves.push({ idx, priority, openFours: atk.openFours, isDoubleFour: atk.isDoubleFour });
      }
    }

    // If defender already threatens an immediate 5-in-a-row, attacker cannot continue slow fours
    if (defenderImmediateWin || maxPlies < 3 || fourMoves.length === 0) {
      ctx.failedCache.set(cacheKey, maxPlies);
      return null;
    }

    fourMoves.sort((a, b) => b.priority - a.priority);
    const limit = Math.min(fourMoves.length, 12);

    for (let i = 0; i < limit; i++) {
      const m = fourMoves[i].idx;
      board[m] = attacker;
      const zA = (m << 1) + (attacker - 1);
      const h1 = (hashHi ^ ZOBRIST_HI[zA]) >>> 0;
      const l1 = (hashLo ^ ZOBRIST_LO[zA]) >>> 0;

      const winSquares = findWinningSquaresAfterMove(board, size, m, attacker);

      if (winSquares.length >= 2) {
        board[m] = EMPTY;
        // Open Four or Double Four = guaranteed win in 3 plies (move -> futile reply -> 5)
        return { move: m, plies: 3, sequence: [m, winSquares[0], winSquares[1]] };
      }

      if (winSquares.length === 1 && maxPlies >= 5) {
        const defBlock = winSquares[0];
        board[defBlock] = defender;

        // If defender's forced block immediately gives defender 5-in-a-row, this branch fails
        if (checkWinAt(board, size, defBlock) === null) {
          const zD = (defBlock << 1) + (defender - 1);
          const h2 = (h1 ^ ZOBRIST_HI[zD]) >>> 0;
          const l2 = (l1 ^ ZOBRIST_LO[zD]) >>> 0;

          const sub = solveVCF(board, size, attacker, maxPlies - 2, h2, l2, ctx);
          board[defBlock] = EMPTY;
          board[m] = EMPTY;

          if (ctx.timedOut) return null;
          if (sub) {
            return {
              move: m,
              plies: sub.plies + 2,
              sequence: [m, defBlock, ...sub.sequence],
            };
          }
        } else {
          board[defBlock] = EMPTY;
          board[m] = EMPTY;
        }
      } else {
        board[m] = EMPTY;
      }
    }

    ctx.failedCache.set(cacheKey, maxPlies);
    return null;
  }

  function runVCFSearch(board, size, attacker, maxPlies, budgetMs, hashHi, hashLo, stampBuf, stampRef) {
    const ctx = {
      deadline: nowMs() + budgetMs,
      timedOut: false,
      nodes: 0,
      stampBuf,
      stampRef,
      failedCache: new Map(),
    };
    // Iterative VCF depth (3, 5, 7, ..., maxPlies) so we always find the SHORTEST forced win!
    for (let plies = 3; plies <= maxPlies; plies += 2) {
      ctx.failedCache.clear();
      const res = solveVCF(board, size, attacker, plies, hashHi, hashLo, ctx);
      if (res) {
        res.nodes = ctx.nodes;
        return res;
      }
      if (ctx.timedOut || nowMs() >= ctx.deadline) break;
    }
    return null;
  }

  /**
   * Verify whether playing `moveIdx` for `defender` genuinely refutes `attacker`'s VCF
   * (including rejecting futile "spite fours" that only delay the VCF by 2 plies).
   */
  function doesMoveRefuteVCF(board, size, defender, moveIdx, maxPlies, budgetMs, hashHi, hashLo, stampBuf, stampRef) {
    const attacker = opponentOf(defender);
    board[moveIdx] = defender;

    // Immediate win for defender refutes everything
    if (checkWinAt(board, size, moveIdx) !== null) {
      board[moveIdx] = EMPTY;
      return true;
    }

    const zD = (moveIdx << 1) + (defender - 1);
    const h1 = (hashHi ^ ZOBRIST_HI[zD]) >>> 0;
    const l1 = (hashLo ^ ZOBRIST_LO[zD]) >>> 0;

    // Check if defender's move creates a counter-four
    const winSquares = findWinningSquaresAfterMove(board, size, moveIdx, defender);
    if (winSquares.length >= 2) {
      // Defender made an unstoppable Open Four / Double Four!
      // Only check whether attacker has an immediate 1-ply win right now
      const oppImmediate = runVCFSearch(board, size, attacker, 1, 8, h1, l1, stampBuf, stampRef);
      board[moveIdx] = EMPTY;
      return oppImmediate === null;
    }

    if (winSquares.length === 1) {
      // Defender made a single counter-four; simulate attacker's forced block to reject spite-checks
      const forcedReply = winSquares[0];
      board[forcedReply] = attacker;
      if (checkWinAt(board, size, forcedReply) !== null) {
        board[forcedReply] = EMPTY;
        board[moveIdx] = EMPTY;
        return false;
      }
      const zA = (forcedReply << 1) + (attacker - 1);
      const h2 = (h1 ^ ZOBRIST_HI[zA]) >>> 0;
      const l2 = (l1 ^ ZOBRIST_LO[zA]) >>> 0;

      // After attacker blocks the counter-four, it's defender's turn again — check if defender has VCF
      // or check whether attacker STILL has an unstoppable VCF if defender passes
      const oppStillHasVcf = runVCFSearch(board, size, attacker, maxPlies - 2, budgetMs, h2, l2, stampBuf, stampRef);
      board[forcedReply] = EMPTY;
      board[moveIdx] = EMPTY;
      return oppStillHasVcf === null;
    }

    const oppVcfAfter = runVCFSearch(board, size, attacker, maxPlies, budgetMs, h1, l1, stampBuf, stampRef);
    board[moveIdx] = EMPTY;
    return oppVcfAfter === null;
  }

  // =========================================================================
  // Threat Breakdown Formatting for Live Engine Inspector (JEV)
  // =========================================================================

  function formatCompactScore(score, vcfPlies) {
    if (vcfPlies && vcfPlies > 0) {
      return vcfPlies === 1 ? 'WIN' : `M${vcfPlies}`;
    }
    if (score >= THREAT_WEIGHTS.WINNING_FIVE * 0.8) return 'WIN';
    if (score <= -THREAT_WEIGHTS.WINNING_FIVE * 0.8) return 'LOSS';

    const abs = Math.abs(score);
    const sign = score >= 0 ? '+' : '−';
    if (abs >= 100000) return `${sign}${Math.round(abs / 1000)}k`;
    if (abs >= 10000) return `${sign}${(abs / 1000).toFixed(0)}k`;
    if (abs >= 1000) return `${sign}${(abs / 1000).toFixed(1)}k`;
    return `${sign}${Math.round(abs)}`;
  }

  function describePointThreats(board, size, idx, player, meta) {
    const r = (idx / size) | 0;
    const c = idx - r * size;
    const opp = opponentOf(player);
    const atk = analyzePoint(board, size, r, c, player);
    const def = analyzePoint(board, size, r, c, opp);

    const tags = [];

    if (meta && meta.vcfWinPlies) {
      if (meta.vcfWinPlies === 1) {
        tags.push('Winning Five');
      } else {
        tags.push(`VCF Forced Win in ${meta.vcfWinPlies}`);
      }
    }
    if (meta && meta.vcfBlockedPlies) {
      tags.push(`VCF Defense (Blocked Win in ${meta.vcfBlockedPlies})`);
    }

    if (tags.length === 0) {
      // Attack patterns
      if (atk.fives > 0) tags.push('Winning Five');
      else if (atk.openFours > 0) tags.push('Open 4');
      else if (atk.isDoubleFour) tags.push('Double 4 Fork');
      else if (atk.isFourThree) tags.push('4-3 Fork');
      else if (atk.isDoubleThree) tags.push('Double Open 3 Fork');
      else if (atk.closedFours > 0) tags.push('Closed 4');
      else if (atk.openThrees > 0) tags.push('Open 3');
      else if (atk.brokenOpenThrees > 0) tags.push('Broken Open 3');

      // Defense patterns
      if (def.fives > 0) tags.push('Block Five');
      else if (def.openFours > 0) tags.push('Block Open 4');
      else if (def.isFork) tags.push('Fork Defense');
      else if (def.closedFours > 0) tags.push('Block Closed 4');
      else if (def.openThrees > 0) tags.push('Block Open 3');
      else if (def.brokenOpenThrees > 0) tags.push('Block Broken 3');
    }

    if (tags.length === 0) {
      if (atk.closedThrees > 0) tags.push('Closed 3');
      else if (atk.openTwos > 0) tags.push('Open 2');
      else if (def.openTwos > 0) tags.push('Contain Open 2');
      else tags.push('Center Control');
    }

    return {
      summary: tags.slice(0, 2).join(' + '),
      tags,
      atk,
      def,
    };
  }

  function buildInspectorPayload(board, size, aiPlayer, scoredList, chosenIdx, meta) {
    const top = [];
    const seen = new Set();
    const sorted = scoredList.slice().sort((a, b) => b.score - a.score);

    // Put chosenIdx first if it was found via VCF or override
    if (chosenIdx >= 0 && !sorted.some((item) => item.idx === chosenIdx)) {
      sorted.unshift({ idx: chosenIdx, score: meta.score || THREAT_WEIGHTS.WINNING_FIVE, vcfPlies: meta.vcfWinPlies });
    }

    // If tactical pruning narrowed scoredList below 8 entries, fill remaining slots with top static neighborhood candidates
    if (sorted.length < 8) {
      const opp = opponentOf(aiPlayer);
      const stampBuf = new Uint32Array(size * size);
      const stampRef = { id: 0 };
      const neighbors = collectNeighborhood(board, size, stampBuf, stampRef, 2);
      const existing = new Set(sorted.map((x) => x.idx));
      const extras = [];
      for (let i = 0; i < neighbors.length; i++) {
        const idx = neighbors[i];
        if (existing.has(idx) || board[idx] !== EMPTY) continue;
        const r = (idx / size) | 0;
        const c = idx - r * size;
        const atk = evaluatePointScore(board, size, r, c, aiPlayer);
        const def = evaluatePointScore(board, size, r, c, opp);
        extras.push({ idx, score: atk * 1.06 + def * 0.98 });
      }
      extras.sort((a, b) => b.score - a.score);
      for (let i = 0; i < extras.length && sorted.length < 8; i++) {
        sorted.push(extras[i]);
      }
    }

    for (let i = 0; i < sorted.length && top.length < 8; i++) {
      const item = sorted[i];
      if (seen.has(item.idx)) continue;
      seen.add(item.idx);
      const r = (item.idx / size) | 0;
      const c = item.idx - r * size;
      const isChosen = item.idx === chosenIdx;
      const desc = describePointThreats(
        board,
        size,
        item.idx,
        aiPlayer,
        isChosen ? meta : null
      );
      top.push({
        index: item.idx,
        row: r,
        col: c,
        score: Math.round(item.score),
        displayScore: formatCompactScore(item.score, isChosen ? meta.vcfWinPlies : item.vcfPlies),
        rank: top.length + 1,
        isChosen,
        summary: desc.summary,
      });
    }

    const chosenDesc =
      chosenIdx >= 0
        ? describePointThreats(board, size, chosenIdx, aiPlayer, meta)
        : { summary: 'Opening', tags: [] };

    return {
      chosenIndex: chosenIdx,
      summary: chosenDesc.summary,
      tags: chosenDesc.tags,
      topCandidates: top,
      vcfWinPlies: meta.vcfWinPlies || null,
      vcfBlockedPlies: meta.vcfBlockedPlies || null,
      ttHits: meta.ttHits || 0,
      nodes: meta.nodes || 1,
      depth: meta.depth || 0,
      durationMs: meta.durationMs || 0,
      level: meta.level || 3,
    };
  }

  // =========================================================================
  // Main Search Entrypoint (Levels 1-5: Casual -> Grandmaster VCF)
  // =========================================================================

  function findBestMove(boardInput, size, aiPlayer, difficultyOrLevel) {
    const startTime = nowMs();
    const board =
      boardInput instanceof Uint8Array ? new Uint8Array(boardInput) : Uint8Array.from(boardInput);
    const total = size * size;
    const cfg = resolveLevelConfig(difficultyOrLevel);

    let stoneCount = 0;
    let firstStoneIdx = -1;
    for (let i = 0; i < total; i++) {
      if (board[i] !== EMPTY) {
        stoneCount++;
        firstStoneIdx = i;
      }
    }

    const center = (size / 2) | 0;

    // Empty board: crisp center opening
    if (stoneCount === 0) {
      const idx = center * size + center;
      const durationMs = nowMs() - startTime;
      const scored = [{ idx, score: 350 }];
      const inspector = buildInspectorPayload(board, size, aiPlayer, scored, idx, {
        depth: 0,
        nodes: 1,
        durationMs,
        level: cfg.id,
      });
      return { index: idx, row: center, col: center, score: 350, depth: 0, nodes: 1, durationMs, inspector };
    }

    // Single stone opening: tight geometric response toward center
    if (stoneCount === 1) {
      const sr = (firstStoneIdx / size) | 0;
      const sc = firstStoneIdx - sr * size;
      const dr = sr <= center ? 1 : -1;
      const dc = sc <= center ? 1 : -1;
      const candidates = [
        [sr + dr, sc + dc],
        [sr + dr, sc],
        [sr, sc + dc],
        [sr - dr, sc + dc],
        [sr + dr, sc - dc],
        [sr - dr, sc],
        [sr, sc - dc],
        [sr - dr, sc - dc],
      ].filter(([rr, cc]) => rr >= 0 && rr < size && cc >= 0 && cc < size && board[rr * size + cc] === EMPTY);

      const pick =
        cfg.id >= 3
          ? candidates[0]
          : candidates[Math.floor(Math.random() * Math.min(3, candidates.length))] || candidates[0];
      const idx = pick[0] * size + pick[1];
      const durationMs = nowMs() - startTime;
      const scored = candidates.slice(0, 8).map(([rr, cc], i) => ({
        idx: rr * size + cc,
        score: Math.max(80, 350 - i * 35),
      }));
      const inspector = buildInspectorPayload(board, size, aiPlayer, scored, idx, {
        depth: 0,
        nodes: candidates.length,
        durationMs,
        level: cfg.id,
      });
      return {
        index: idx,
        row: pick[0],
        col: pick[1],
        score: 350,
        depth: 0,
        nodes: candidates.length,
        durationMs,
        inspector,
      };
    }

    const stampBuf = new Uint32Array(total);
    const stampRef = { id: 0 };
    const humanPlayer = opponentOf(aiPlayer);
    const initHash = computeBoardHash(board);

    let rootCandidates = generateCandidates(board, size, aiPlayer, cfg.rootBranch, stampBuf, stampRef, -1);

    if (rootCandidates.length === 0) {
      for (let i = 0; i < total; i++) {
        if (board[i] === EMPTY) {
          const r = (i / size) | 0;
          const c = i - r * size;
          const durationMs = nowMs() - startTime;
          return {
            index: i,
            row: r,
            col: c,
            score: 0,
            depth: 0,
            nodes: 1,
            durationMs,
            inspector: buildInspectorPayload(board, size, aiPlayer, [{ idx: i, score: 0 }], i, {
              depth: 0,
              nodes: 1,
              durationMs,
              level: cfg.id,
            }),
          };
        }
      }
      return null;
    }

    // Immediate winning 5-in-a-row
    if (rootCandidates[0].immediateWin) {
      const idx = rootCandidates[0].idx;
      const r = (idx / size) | 0;
      const c = idx - r * size;
      const durationMs = nowMs() - startTime;
      const inspector = buildInspectorPayload(board, size, aiPlayer, rootCandidates, idx, {
        score: THREAT_WEIGHTS.WINNING_FIVE,
        vcfWinPlies: 1,
        depth: 1,
        nodes: 1,
        durationMs,
        level: cfg.id,
      });
      return {
        index: idx,
        row: r,
        col: c,
        score: THREAT_WEIGHTS.WINNING_FIVE,
        depth: 1,
        nodes: 1,
        durationMs,
        inspector,
      };
    }

    if (rootCandidates.length === 1) {
      const idx = rootCandidates[0].idx;
      const r = (idx / size) | 0;
      const c = idx - r * size;
      const durationMs = nowMs() - startTime;
      const isOpen4Win = cfg.useVCF && rootCandidates[0].atk >= THREAT_WEIGHTS.OPEN_FOUR && rootCandidates[0].def < THREAT_WEIGHTS.WINNING_FIVE;
      const inspector = buildInspectorPayload(board, size, aiPlayer, rootCandidates, idx, {
        score: rootCandidates[0].score,
        vcfWinPlies: isOpen4Win ? 3 : null,
        depth: isOpen4Win ? 3 : 1,
        nodes: 1,
        durationMs,
        level: cfg.id,
      });
      return {
        index: idx,
        row: r,
        col: c,
        score: rootCandidates[0].score,
        depth: isOpen4Win ? 3 : 1,
        nodes: 1,
        durationMs,
        inspector,
      };
    }

    // -----------------------------------------------------------------------
    // Level 1 · Casual (Depth 1, ~1 ms, basic pattern weights with light jitter)
    // -----------------------------------------------------------------------
    if (cfg.id === 1) {
      let chosen = rootCandidates[0];
      const isUrgent = chosen.atk >= THREAT_WEIGHTS.CLOSED_FOUR || chosen.def >= THREAT_WEIGHTS.OPEN_THREE;
      if (!isUrgent && rootCandidates.length > 1) {
        const pool = Math.min(4, rootCandidates.length);
        let sum = 0;
        for (let i = 0; i < pool; i++) sum += pool - i;
        let roll = Math.random() * sum;
        for (let i = 0; i < pool; i++) {
          roll -= pool - i;
          if (roll <= 0) {
            chosen = rootCandidates[i];
            break;
          }
        }
      }
      const r = (chosen.idx / size) | 0;
      const c = chosen.idx - r * size;
      const durationMs = nowMs() - startTime;
      const inspector = buildInspectorPayload(board, size, aiPlayer, rootCandidates, chosen.idx, {
        score: chosen.score,
        depth: 1,
        nodes: rootCandidates.length,
        durationMs,
        level: cfg.id,
      });
      return {
        index: chosen.idx,
        row: r,
        col: c,
        score: chosen.score,
        depth: 1,
        nodes: rootCandidates.length,
        durationMs,
        inspector,
      };
    }

    // -----------------------------------------------------------------------
    // Level 5 · Grandmaster Dedicated VCF (14-ply Attack & Defense)
    // -----------------------------------------------------------------------
    let vcfBlockedPlies = null;
    let vcfNodes = 0;

    if (cfg.useVCF) {
      // 1) Offensive VCF: Can AI force a continuous-fours win up to 14 plies?
      const aiVcf = runVCFSearch(
        board,
        size,
        aiPlayer,
        cfg.vcfPlies,
        75,
        initHash.hi,
        initHash.lo,
        stampBuf,
        stampRef
      );
      if (aiVcf) {
        const idx = aiVcf.move;
        const r = (idx / size) | 0;
        const c = idx - r * size;
        const durationMs = nowMs() - startTime;
        const score = THREAT_WEIGHTS.WINNING_FIVE - aiVcf.plies * 1000;
        const listWithVcf = rootCandidates.map((m) =>
          m.idx === idx ? { idx: m.idx, score, vcfPlies: aiVcf.plies } : { idx: m.idx, score: m.staticScore || m.score }
        );
        const inspector = buildInspectorPayload(board, size, aiPlayer, listWithVcf, idx, {
          score,
          vcfWinPlies: aiVcf.plies,
          depth: aiVcf.plies,
          nodes: aiVcf.nodes || 1,
          durationMs,
          level: cfg.id,
        });
        return {
          index: idx,
          row: r,
          col: c,
          score,
          depth: aiVcf.plies,
          nodes: aiVcf.nodes || 1,
          durationMs,
          inspector,
        };
      }

      // 2) Defensive VCF: Does opponent currently threaten a forced VCF / 4-3 win?
      const oppVcf = runVCFSearch(
        board,
        size,
        humanPlayer,
        Math.min(12, cfg.vcfPlies),
        55,
        initHash.hi,
        initHash.lo,
        stampBuf,
        stampRef
      );

      if (oppVcf) {
        vcfNodes += oppVcf.nodes || 0;
        // Collect candidate refutations: opponent's VCF sequence squares + top tactical candidates
        const testSet = new Set();
        const defensePool = [];

        for (let i = 0; i < oppVcf.sequence.length; i++) {
          const sq = oppVcf.sequence[i];
          if (board[sq] === EMPTY && !testSet.has(sq)) {
            testSet.add(sq);
            const r = (sq / size) | 0;
            const c = sq - r * size;
            const atk = evaluatePointScore(board, size, r, c, aiPlayer);
            const def = evaluatePointScore(board, size, r, c, humanPlayer);
            defensePool.push({ idx: sq, score: atk + def * 1.15, staticScore: atk + def, atk, def });
          }
        }
        for (let i = 0; i < rootCandidates.length; i++) {
          const m = rootCandidates[i];
          if (!testSet.has(m.idx)) {
            testSet.add(m.idx);
            defensePool.push(m);
          }
        }

        const refutations = [];
        const defDeadline = startTime + 150;
        for (let i = 0; i < defensePool.length && nowMs() < defDeadline; i++) {
          const cand = defensePool[i];
          const ok = doesMoveRefuteVCF(
            board,
            size,
            aiPlayer,
            cand.idx,
            Math.min(10, oppVcf.plies + 2),
            16,
            initHash.hi,
            initHash.lo,
            stampBuf,
            stampRef
          );
          if (ok) {
            refutations.push(cand);
          }
        }

        if (refutations.length > 0) {
          rootCandidates = refutations;
          vcfBlockedPlies = oppVcf.plies;
        }
      }
    }

    // -----------------------------------------------------------------------
    // Iterative Deepening Alpha-Beta (with Zobrist TT for Master D6 & Grandmaster)
    // -----------------------------------------------------------------------
    const deadline = startTime + cfg.timeBudgetMs;
    const useTT = cfg.useTT;
    if (useTT) {
      currentTTGen = (currentTTGen + 1) & 0xffff;
      if (currentTTGen === 0) {
        ttGen.fill(0);
        currentTTGen = 1;
      }
    }

    let nodes = vcfNodes;
    let ttHits = 0;
    let timedOut = false;

    function alphaBeta(depth, alpha, beta, maximizing, lastMoveIdx, hashHi, hashLo) {
      nodes++;
      if ((nodes & 63) === 0 && nowMs() >= deadline) {
        timedOut = true;
        return 0;
      }

      if (lastMoveIdx >= 0) {
        const win = checkWinAt(board, size, lastMoveIdx);
        if (win) {
          const bonus = depth * 1000;
          return win.winner === aiPlayer
            ? THREAT_WEIGHTS.WINNING_FIVE + bonus
            : -(THREAT_WEIGHTS.WINNING_FIVE + bonus);
        }
      }

      const origAlpha = alpha;
      let ttMove = -1;
      // Mix side-to-move into TT slot lookup
      const sideMixHi = maximizing ? hashHi : (hashHi ^ 0xa5a5a5a5) >>> 0;
      const sideMixLo = maximizing ? hashLo : (hashLo ^ 0x5a5a5a5a) >>> 0;
      const slot = sideMixLo & TT_MASK;

      if (useTT && ttGen[slot] === currentTTGen && ttKeyHi[slot] === sideMixHi && ttKeyLo[slot] === sideMixLo) {
        ttMove = ttBestMove[slot];
        if (ttDepth[slot] >= depth) {
          ttHits++;
          const storedScore = ttScore[slot];
          const flag = ttFlag[slot];
          if (flag === TT_EXACT) return storedScore;
          if (flag === TT_LOWER && storedScore > alpha) alpha = storedScore;
          else if (flag === TT_UPPER && storedScore < beta) beta = storedScore;
          if (alpha >= beta) return storedScore;
        }
      }

      const currentPlayer = maximizing ? aiPlayer : humanPlayer;

      if (depth === 0) {
        return evaluateBoard(board, size, aiPlayer, currentPlayer);
      }

      const moves = generateCandidates(board, size, currentPlayer, cfg.innerBranch, stampBuf, stampRef, ttMove);
      if (moves.length === 0) return 0;

      let bestVal = maximizing ? -Infinity : Infinity;
      let bestMove = moves[0].idx;
      const pOffset = currentPlayer - 1;

      if (maximizing) {
        for (let i = 0; i < moves.length; i++) {
          const mIdx = moves[i].idx;
          const zIdx = (mIdx << 1) + pOffset;
          board[mIdx] = currentPlayer;
          const val = alphaBeta(
            depth - 1,
            alpha,
            beta,
            false,
            mIdx,
            (hashHi ^ ZOBRIST_HI[zIdx]) >>> 0,
            (hashLo ^ ZOBRIST_LO[zIdx]) >>> 0
          );
          board[mIdx] = EMPTY;

          if (timedOut) return 0;
          if (val > bestVal) {
            bestVal = val;
            bestMove = mIdx;
          }
          if (bestVal > alpha) alpha = bestVal;
          if (beta <= alpha) break;
        }
      } else {
        for (let i = 0; i < moves.length; i++) {
          const mIdx = moves[i].idx;
          const zIdx = (mIdx << 1) + pOffset;
          board[mIdx] = currentPlayer;
          const val = alphaBeta(
            depth - 1,
            alpha,
            beta,
            true,
            mIdx,
            (hashHi ^ ZOBRIST_HI[zIdx]) >>> 0,
            (hashLo ^ ZOBRIST_LO[zIdx]) >>> 0
          );
          board[mIdx] = EMPTY;

          if (timedOut) return 0;
          if (val < bestVal) {
            bestVal = val;
            bestMove = mIdx;
          }
          if (bestVal < beta) beta = bestVal;
          if (beta <= alpha) break;
        }
      }

      if (useTT && !timedOut) {
        let flag = TT_EXACT;
        if (bestVal <= origAlpha) flag = TT_UPPER;
        else if (bestVal >= beta) flag = TT_LOWER;

        if (ttGen[slot] !== currentTTGen || ttDepth[slot] <= depth) {
          ttKeyHi[slot] = sideMixHi;
          ttKeyLo[slot] = sideMixLo;
          ttDepth[slot] = depth;
          ttFlag[slot] = flag;
          ttScore[slot] = bestVal;
          ttBestMove[slot] = bestMove;
          ttGen[slot] = currentTTGen;
        }
      }

      return bestVal;
    }

    let bestMoveIdx = rootCandidates[0].idx;
    let bestScore = rootCandidates[0].staticScore || rootCandidates[0].score;
    let completedDepth = 1;
    const orderedRoot = rootCandidates.slice();
    let finalScoredRoot = orderedRoot.map((c) => ({ idx: c.idx, cand: c, score: c.staticScore || c.score }));
    const aiOffset = aiPlayer - 1;

    for (let depth = 2; depth <= cfg.maxDepth; depth++) {
      timedOut = false;
      let iterBestIdx = orderedRoot[0].idx;
      let iterBestScore = -Infinity;
      let alpha = -Infinity;
      const beta = Infinity;
      const scoredThisIter = [];

      for (let i = 0; i < orderedRoot.length; i++) {
        const cand = orderedRoot[i];
        const zIdx = (cand.idx << 1) + aiOffset;
        board[cand.idx] = aiPlayer;
        const val = alphaBeta(
          depth - 1,
          alpha,
          beta,
          false,
          cand.idx,
          (initHash.hi ^ ZOBRIST_HI[zIdx]) >>> 0,
          (initHash.lo ^ ZOBRIST_LO[zIdx]) >>> 0
        );
        board[cand.idx] = EMPTY;

        if (timedOut) break;

        const tieAdjusted = val + (cand.staticScore || cand.score) * 0.0002;
        scoredThisIter.push({ idx: cand.idx, cand, score: val, sortScore: tieAdjusted });

        if (tieAdjusted > iterBestScore) {
          iterBestScore = tieAdjusted;
          iterBestIdx = cand.idx;
        }
        if (val > alpha) alpha = val;
        if (val >= THREAT_WEIGHTS.WINNING_FIVE) break;
      }

      if (!timedOut) {
        bestMoveIdx = iterBestIdx;
        bestScore = scoredThisIter.reduce((acc, x) => (x.idx === iterBestIdx ? x.score : acc), iterBestScore);
        completedDepth = depth;

        scoredThisIter.sort((a, b) => b.sortScore - a.sortScore);
        finalScoredRoot = scoredThisIter;
        for (let i = 0; i < scoredThisIter.length; i++) {
          orderedRoot[i] = scoredThisIter[i].cand;
        }

        if (bestScore >= THREAT_WEIGHTS.WINNING_FIVE * 0.9) break;
      } else {
        // Keep partial depth improvement if first root moves already beat previous score safely?
        // Safer: retain last fully completed iteration so we never pick an unverified move.
        break;
      }

      if (nowMs() >= deadline) break;
    }

    // Level 2 · Club: tiny variety on quiet near-equal positions so games stay fresh
    if (cfg.id === 2 && finalScoredRoot.length > 1 && Math.abs(bestScore) < THREAT_WEIGHTS.OPEN_THREE) {
      const topScore = finalScoredRoot[0].score;
      const closeAlts = [];
      for (let i = 0; i < Math.min(3, finalScoredRoot.length); i++) {
        if (topScore - finalScoredRoot[i].score <= 90) {
          closeAlts.push(finalScoredRoot[i].idx);
        }
      }
      if (closeAlts.length > 1 && Math.random() < 0.25) {
        bestMoveIdx = closeAlts[Math.floor(Math.random() * closeAlts.length)];
      }
    }

    const r = (bestMoveIdx / size) | 0;
    const c = bestMoveIdx - r * size;
    const durationMs = nowMs() - startTime;

    const inspector = buildInspectorPayload(board, size, aiPlayer, finalScoredRoot, bestMoveIdx, {
      score: bestScore,
      vcfBlockedPlies,
      ttHits,
      nodes,
      depth: completedDepth,
      durationMs,
      level: cfg.id,
    });

    return {
      index: bestMoveIdx,
      row: r,
      col: c,
      score: bestScore,
      depth: completedDepth,
      nodes,
      ttHits,
      durationMs,
      inspector,
    };
  }

  const api = {
    EMPTY,
    PLAYER_X,
    PLAYER_O,
    THREAT_WEIGHTS,
    DIFFICULTY_LEVELS,
    opponentOf,
    resolveLevelConfig,
    checkWinAt,
    checkWinBoard,
    analyzePoint,
    evaluatePointScore,
    evaluateBoard,
    findBestMove,
  };

  // Dual-mode export: Web Worker, Node.js CommonJS, or Browser Window global
  const isWorker =
    typeof WorkerGlobalScope !== 'undefined' &&
    typeof self !== 'undefined' &&
    self instanceof WorkerGlobalScope;

  if (isWorker) {
    self.onmessage = function (event) {
      const data = event.data;
      if (!data || data.type !== 'FIND_BEST_MOVE') return;
      try {
        const result = findBestMove(data.board, data.size, data.player, data.level);
        self.postMessage({
          type: 'BEST_MOVE_RESULT',
          requestId: data.requestId,
          purpose: data.purpose || 'move',
          result,
        });
      } catch (err) {
        self.postMessage({
          type: 'BEST_MOVE_ERROR',
          requestId: data.requestId,
          error: err && err.message ? err.message : String(err),
        });
      }
    };
  } else if (typeof module !== 'undefined' && module.exports) {
    module.exports = api;
  } else {
    globalScope.LuffarschackEngine = api;
  }
})(typeof window !== 'undefined' ? window : globalThis);
