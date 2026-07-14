# SqChess baseline checkpoint

Branch: experiment-v3-relief-guard

This checkpoint consolidates the current guard-based experimental engine.

## Consolidated guards

- Relief imbalance guard
- Repeat minor guard
- Sortie / tactical sortie guard
- General toxic capture guard
- Pawn fork threat guard
- Midgame sortie guard
- Shield drift guard
- Forcing capture mirage guard

## Rejected experiments

- Tactical transfer damping
- Global repeat-minor increase from 2.40 to 3.10
- Loose minor after-move guard

## Current baseline result

Against Stockfish with limited strength, SqChess plays a coherent game and wins the tested line at:

- SF_ELO=1100
- SF_ELO=1320
- SF_ELO=1500

Representative final line:

d2d4 d7d6 b1c3 c7c6 g1f3 b7b6 e2e4 a7a6 c1e3 d6d5 e4d5 e7e6 f1d3 e6e5 d4e5 f7f6 e1g1 f6f5 d5d6 c6c5 a2a3 b6b5 e3c5 g7g6 c5e3 g6g5 e3g5 h7h6 g5d8 h6h5 d8g5 a6a5 d3b5 e8f7 d1d5 f7g6 b5e8 g6g7 d5f7

Open issue:

Against stronger Stockfish, the next known failure mode is queen intrusion followed by king oscillation, e.g. g1-h1 / h1-g1 under attack.
