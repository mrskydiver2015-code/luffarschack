# Luffarschack - Five in a Row

Responsive browser-based Gomoku (5-in-a-row) built in vanilla HTML, CSS, and JavaScript.

## Features
- Board sizes: 15x15, 19x19 (default), and 25x25 with Light and Dark themes.
- Mobile-first controls: Pinch/button zoom and Confirm Tap placement to prevent mis-taps.
- 5-Tier Web Worker Engine: Runs off the main thread (1 Casual to 5 Grandmaster with depth-6 search, Zobrist transposition table, weighted threat matrix, and 14-ply recursive VCF solver).
- Inspect Engine: Real-time board overlay displaying top candidate move scores and search telemetry.

## Run Locally
Serve the root folder with any static HTTP server (required for the Web Worker), for example: npx serve .
