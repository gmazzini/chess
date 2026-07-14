#!/usr/bin/env python3
import sys
import re
import os

USE_COLOR = os.environ.get("NO_COLOR") is None

WHITE_BG = "\033[48;5;250m"
BLACK_BG = "\033[48;5;240m"
WHITE_FG = "\033[38;5;15m"
BLACK_FG = "\033[38;5;16m"
RESET = "\033[0m"
CLEAR = "\033[H\033[J"

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

def piece_char(p):
    return "." if p == "." else p

def apply_move(board, move):
    if len(move) < 4:
        return

    fr = move[0:2]
    to = move[2:4]
    promo = move[4] if len(move) >= 5 else None

    r1, c1 = sq_to_rc(fr)
    r2, c2 = sq_to_rc(to)

    p = board[r1][c1]
    if p == ".":
        return

    # en passant
    if p.lower() == "p" and c1 != c2 and board[r2][c2] == ".":
        if p.isupper():
            board[r2 + 1][c2] = "."
        else:
            board[r2 - 1][c2] = "."

    # castling
    if p.lower() == "k" and abs(c2 - c1) == 2:
        if c2 == 6:   # king side
            board[r1][5] = board[r1][7]
            board[r1][7] = "."
        elif c2 == 2: # queen side
            board[r1][3] = board[r1][0]
            board[r1][0] = "."

    board[r1][c1] = "."

    if promo:
        p = promo.upper() if p.isupper() else promo.lower()

    board[r2][c2] = p

def render(board, last_line=""):
    out = []
    out.append(CLEAR if USE_COLOR else "")
    out.append("SqChess live board\n")
    if last_line:
        out.append(last_line + "\n")
    out.append("\n")

    for r in range(8):
        rank = 8 - r
        out.append(f" {rank} ")
        for c in range(8):
            p = board[r][c]
            ch = " " if p == "." else piece_char(p)

            if USE_COLOR:
                bg = WHITE_BG if (r + c) % 2 == 0 else BLACK_BG
                fg = WHITE_FG if p.isupper() else BLACK_FG
                if p == ".":
                    fg = ""
                out.append(f"{bg}{fg} {ch} {RESET}")
            else:
                out.append(f" {ch} ")
        out.append(f" {rank}\n")

    out.append("\n    a  b  c  d  e  f  g  h\n")
    out.append("\nMaiuscole = SqChess/White, minuscole = Stockfish/Black\n")
    return "".join(out)

def main():
    board = initial_board()

    print(render(board, "startpos"), flush=True)

    ply_re = re.compile(r"^PLY\s+(\d+)\s+(SQ|SF)\s+([a-h][1-8][a-h][1-8][qrbn]?)\b")
    score_re = re.compile(r"\bscore=([-+0-9.]+)")

    for line in sys.stdin:
        line = line.rstrip("\n")
        m = ply_re.search(line)

        if m:
            ply = int(m.group(1))
            side = m.group(2)
            move = m.group(3)

            apply_move(board, move)

            score = ""
            sm = score_re.search(line)
            if sm:
                score = f" score={sm.group(1)}"

            title = f"PLY {ply:02d} {side} {move}{score}"
            print(render(board, title), flush=True)
        elif "non ha prodotto una mossa" in line:
            print(line, flush=True)

if __name__ == "__main__":
    main()
