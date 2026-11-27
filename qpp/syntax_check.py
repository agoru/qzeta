"""The checker of the syntax of proof words (qpp/syntax.py), as a script: python3 qpp/syntax_check.py ... (the same
as python3 -m qpp.syntax ...)"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from qpp.syntax import *  # noqa: E402,F401,F403
from qpp.syntax import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
