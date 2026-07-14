#!/usr/bin/env python3
import sys
import re
import os

USE_COLOR = os.environ.get("NO_COLOR") is None

WHITE_BG = "\033[48;5;250m"
BLACK_BG = "\033[48;5;240m"
WHITE_FG = "\033[38;5;15m"
BLACK_FG = "\033[38;5;16m"
LAST_BG = "\033[48;5;220m"
RESET = "\033[0m"
CLEAR = "\033[H\033[J"

PIECE_VALUE = {
    "p": 1.0,
    "n": 3.0,
    "b": 3.0,
    "r": 5.0,
    "q": 9.0,
    "k": 0.0,
}

def initial_board():
    return [
        list("rnbqkbnr"),
        list("pppppppp"),
        list("........"),
        list("........"),
        list("........"),
        list("........"),
        list("PPPPPPPP"),
        list("RNBQKBNR"),
    ]

def sq_to_rc(sq):
    file = ord(sq[0]) - ord("a")
    rank = int(sq[1])
    return 8 - rank, file

def rc_to_sq(r, c):
    return chr(ord("a") + c) + str(8 - r)

def material_estimate(board):
    total = 0.0
    for row in board:
        for p in row:
            if p == ".":
                continue
            v = PIECE_VALUE.get(p.lower(), 0.0)
            if p.isupper():
                total += v
            else:
                total -= v
    return total

def apply_move(board, move):
    if len(move) < 4:
        return None

    fr = move[0:2]
    to = move[2:4]
    promo = move[4] if len(move) >= 5 else None

    r1, c1 = sq_to_rc(fr)
    r2, c2 = sq_to_rc(to)

    p = board[r1][c1]
    if p == ".":
        return None

    # en passant
    if p.lower() == "p" and c1 != c2 and board[r2][c2] == ".":
        if p.isupper():
            board[r2 + 1][c2] = "."
        else:
            board[r2 - 1][c2] = "."

    # castling
    if p.lower() == "k" and abs(c2 - c1) == 2:
        if c2 == 6:
            board[r1][5] = board[r1][7]
            board[r1][7] = "."
        elif c2 == 2:
            board[r1][3] = board[r1][0]
            board[r1][0] = "."

    board[r1][c1] = "."

    if promo:
        p = promo.upper() if p.isupper() else promo.lower()

    board[r2][c2] = p
    return (fr, to)

def render(board, current="", last_sq="-", last_sf="-", last_score="-", last_move=None):
    mat = material_estimate(board)

    out = []
    out.append(CLEAR if USE_COLOR else "")
    out.append("SqChess live board\n")
    out.append("\n")
    out.append(f"Current:       {current}\n")
    out.append(f"Last SQ move:  {last_sq}\n")
    out.append(f"Last SF move:  {last_sf}\n")
    out.append(f"Last SQ score: {last_score}\n")
    out.append(f"Material est.: {mat:+.1f} pawns  (white/SqChess perspective)\n")
    out.append("\n")

    last_squares = set()
    if last_move:
        last_squares.add(last_move[1])

    for r in range(8):
        rank = 8 - r
        out.append(f" {rank} ")
        for c in range(8):
            sq = rc_to_sq(r, c)
            p = board[r][c]
            ch = " " if p == "." else p

            if USE_COLOR:
                if sq in last_squares:
                    bg = LAST_BG
                else:
                    bg = WHITE_BG if (r + c) % 2 == 0 else BLACK_BG
                fg = WHITE_FG if p.isupper() else BLACK_FG
                if p == ".":
                    fg = ""
                out.append(f"{bg}{fg} {ch} {RESET}")
            else:
                if sq in last_squares:
                    out.append(f"[{ch}]")
                else:
                    out.append(f" {ch} ")
        out.append(f" {rank}\n")

    out.append("\n    a  b  c  d  e  f  g  h\n")
    out.append("\nMaiuscole = SqChess/White, minuscole = Stockfish/Black\n")
    out.append("Caselle evidenziate = ultima mossa\n")
    return "".join(out)

def main():
    board = initial_board()
    last_sq = "-"
    last_sf = "-"
    last_score = "-"
    last_move = None

    print(render(board, "startpos", last_sq, last_sf, last_score, last_move), flush=True)

    ply_re = re.compile(r"^PLY\s+(\d+)\s+(SQ|SF)\s+([a-h][1-8][a-h][1-8][qrbn]?)\b")
    score_re = re.compile(r"\bscore=([-+0-9.]+)")

    for line in sys.stdin:
        line = line.rstrip("\n")
        m = ply_re.search(line)

        if m:
            ply = int(m.group(1))
            side = m.group(2)
            move = m.group(3)

            lm = apply_move(board, move)
            if lm:
                last_move = lm

            sm = score_re.search(line)
            if side == "SQ":
                last_sq = move
                if sm:
                    last_score = sm.group(1)
            else:
                last_sf = move

            current = f"PLY {ply:02d} {side} {move}"
            if side == "SQ" and sm:
                current += f" score={sm.group(1)}"

            print(render(board, current, last_sq, last_sf, last_score, last_move), flush=True)

        elif "non ha prodotto una mossa" in line:
            print(line, flush=True)

if __name__ == "__main__":
    main()
