SqChess is an experimental chess engine based on a transformed-state view of the game.
Instead of relying primarily on classical handcrafted positional rules, each position is mapped into a multidimensional state Φ describing value, risk, forcing potential, stability, activity, coherence, resilience, and tactical pressure.
Move selection is then interpreted as choosing the transformation that moves the game toward a better region of this state space.
The engine searches normal legal continuations, but evaluates reached positions through this abstract geometry rather than through a conventional chess heuristic stack.
The goal is not to tune a strong engine in the standard way, but to explore whether chess play can emerge from a compact, general transformation model.
