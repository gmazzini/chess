#!/usr/bin/env python3
import argparse
import os
import re
import subprocess
import sys
import threading
import queue
import time

BESTMOVE_RE = re.compile(r"^bestmove\s+(\S+)")
SF_SCORE_RE = re.compile(r"\bscore\s+(cp|mate)\s+(-?\d+)")
FEN_RE = re.compile(r"^Fen:\s+(.+)$")

def run_sqchess(sq_path, fen, timeout):
    try:
        p = subprocess.run(
            [sq_path, fen],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as e:
        out = e.stdout if isinstance(e.stdout, str) else ""
        err = e.stderr if isinstance(e.stderr, str) else ""
        return None, None, None, out, err + "\nTIMEOUT\n", 124

    best = None
    score = None
    depth = None

    for line in p.stdout.splitlines():
        parts = line.strip().split()
        if len(parts) >= 2 and parts[0] == "bestmove":
            best = parts[1]
        elif len(parts) >= 2 and parts[0] == "score":
            score = parts[1]
        elif len(parts) >= 2 and parts[0] == "search_depth":
            depth = parts[1]

    return best, score, depth, p.stdout, p.stderr, p.returncode

class Stockfish:
    def __init__(self, path):
        self.path = path
        self.q = queue.Queue()
        self.p = subprocess.Popen(
            [path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

        self.reader = threading.Thread(target=self._reader_loop, daemon=True)
        self.reader.start()

        self._send("uci")
        self._read_until(lambda line: line.startswith("uciok"), 10, "uciok")

        self._send("isready")
        self._read_until(lambda line: line.startswith("readyok"), 10, "readyok")

    def _reader_loop(self):
        try:
            for line in self.p.stdout:
                self.q.put(line)
        except Exception as e:
            self.q.put("__READER_ERROR__ {}\n".format(e))

    def _send(self, cmd):
        self.p.stdin.write(cmd + "\n")
        self.p.stdin.flush()

    def _drain(self):
        while True:
            try:
                self.q.get_nowait()
            except queue.Empty:
                break

    def _read_until(self, predicate, timeout, label):
        deadline = time.time() + timeout
        lines = []

        while time.time() < deadline:
            remaining = max(0.01, deadline - time.time())
            try:
                line = self.q.get(timeout=remaining)
            except queue.Empty:
                break

            lines.append(line)

            if predicate(line):
                return lines

        raise TimeoutError(
            "Stockfish timeout waiting for {}. Partial output:\n{}".format(
                label, "".join(lines)
            )
        )

    def close(self):
        try:
            self._send("quit")
            self.p.wait(timeout=2)
        except Exception:
            try:
                self.p.kill()
            except Exception:
                pass

    def fen(self, moves):
        self._drain()
        self._send("position startpos moves " + " ".join(moves))
        self._send("d")
        lines = self._read_until(lambda line: line.startswith("Checkers:"), 10, "FEN/Checkers")

        fen = None
        for line in lines:
            m = FEN_RE.search(line)
            if m:
                fen = m.group(1).strip()

        if not fen:
            raise RuntimeError("Stockfish did not return FEN. Output:\n{}".format("".join(lines)))
        return fen

    def bestmove(self, moves, movetime_ms):
        self._drain()
        self._send("position startpos moves " + " ".join(moves))

        t0 = time.time()
        self._send("go movetime {}".format(movetime_ms))

        deadline = time.time() + max(5.0, movetime_ms / 1000.0 + 2.0)
        lines = []
        best = None
        last_score = None

        while time.time() < deadline:
            remaining = max(0.01, deadline - time.time())
            try:
                line = self.q.get(timeout=remaining)
            except queue.Empty:
                break

            lines.append(line)

            sm = SF_SCORE_RE.search(line)
            if sm:
                kind = sm.group(1)
                val = int(sm.group(2))
                if kind == "cp":
                    last_score = "{:+.2f}".format(val / 100.0)
                else:
                    last_score = "mate{}".format(val)

            bm = BESTMOVE_RE.search(line)
            if bm:
                best = bm.group(1)
                elapsed_ms = int((time.time() - t0) * 1000)
                return best, last_score, elapsed_ms, "".join(lines)

        elapsed_ms = int((time.time() - t0) * 1000)
        return None, last_score, elapsed_ms, "".join(lines)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sf", default=os.environ.get("STOCKFISH", "/usr/games/stockfish"))
    ap.add_argument("--sq", default=os.environ.get("SQCHESS", "./sqchess"))
    ap.add_argument("--sf-movetime", type=int, default=int(os.environ.get("SFCHESS_TIMEOUT", "200")))
    ap.add_argument("--sq-timeout", type=float, default=float(os.environ.get("SQCHESS_TIMEOUT", "60")))
    ap.add_argument("--max-ply", type=int, default=int(os.environ.get("MAX_PLY", "120")))
    ap.add_argument("--start-moves", default=os.environ.get("START_MOVES", ""))
    args = ap.parse_args()

    moves = args.start_moves.split() if args.start_moves.strip() else []

    print("MATCH_DRIVER tools/play_match.py persistent_stockfish_queue")
    print("SF movetime={}ms".format(args.sf_movetime))
    print("SQ timeout={}s".format(args.sq_timeout))
    print("MAX_PLY={}".format(args.max_ply))
    print("START_MOVES={}".format(" ".join(moves) if moves else "-"))
    print("", flush=True)

    try:
        sf = Stockfish(args.sf)
    except Exception as e:
        print("ERROR: cannot initialize Stockfish: {}".format(e), flush=True)
        return 2

    try:
        for ply in range(len(moves) + 1, args.max_ply + 1):
            white_to_move = (ply % 2 == 1)

            if white_to_move:
                try:
                    fen = sf.fen(moves)
                except Exception as e:
                    print("PLY {:02d} SQ ERROR unable_to_get_fen {}".format(ply, e), flush=True)
                    return 2

                t0 = time.time()
                best, score, depth, out, err, rc = run_sqchess(args.sq, fen, args.sq_timeout)
                elapsed = int((time.time() - t0) * 1000)

                if not best or best == "(none)":
                    print(
                        "PLY {:02d} SQ none score={} depth={} time_ms={} fen=\"{}\"".format(
                            ply,
                            score if score is not None else "?",
                            depth if depth is not None else "?",
                            elapsed,
                            fen,
                        ),
                        flush=True,
                    )
                    print("SQChess non ha prodotto una mossa.", flush=True)
                    if out.strip():
                        print("SQ_STDOUT_BEGIN\n{}\nSQ_STDOUT_END".format(out.strip()), flush=True)
                    if err.strip():
                        print("SQ_STDERR_BEGIN\n{}\nSQ_STDERR_END".format(err.strip()), flush=True)
                    return 0

                moves.append(best)
                print(
                    "PLY {:02d} SQ {} score={} depth={} time_ms={} fen=\"{}\"".format(
                        ply,
                        best,
                        score if score is not None else "?",
                        depth if depth is not None else "?",
                        elapsed,
                        fen,
                    ),
                    flush=True,
                )

            else:
                best, sf_score, elapsed, sf_out = sf.bestmove(moves, args.sf_movetime)

                if not best or best == "(none)":
                    try:
                        fen = sf.fen(moves)
                    except Exception:
                        fen = "?"
                    print(
                        "PLY {:02d} SF none sf_score={} time_ms={} fen=\"{}\"".format(
                            ply,
                            sf_score if sf_score is not None else "?",
                            elapsed,
                            fen,
                        ),
                        flush=True,
                    )
                    print("Stockfish non ha prodotto una mossa.", flush=True)
                    if sf_out.strip():
                        print("SF_OUTPUT_BEGIN\n{}\nSF_OUTPUT_END".format(sf_out.strip()), flush=True)
                    return 0

                moves.append(best)

                try:
                    fen_after = sf.fen(moves)
                except Exception:
                    fen_after = "?"

                print(
                    "PLY {:02d} SF {} sf_score={} time_ms={} fen_after=\"{}\"".format(
                        ply,
                        best,
                        sf_score if sf_score is not None else "?",
                        elapsed,
                        fen_after,
                    ),
                    flush=True,
                )

        print("MAX_PLY reached.", flush=True)
        print("MOVES {}".format(" ".join(moves)), flush=True)
        return 0

    finally:
        sf.close()

if __name__ == "__main__":
    raise SystemExit(main())
