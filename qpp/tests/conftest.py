import importlib.util
import sys
from pathlib import Path

# The package qpp is imported from the repository root, whichever way pytest was started (python3 -m pytest puts the
# current folder on the path, pytest alone does not) and whichever inifile it chose.
_ROOT = str(Path(__file__).resolve().parents[2])
if _ROOT in sys.path:
    sys.path.remove(_ROOT)
sys.path.insert(0, _ROOT)

# The memo of the repository that holds this folder (tools/memo_pytest.py at its root), if there is one: a test module
# whose inputs (the files it reads, the modules it imports, the toolchain) are those of a recorded pass is not run
# again. MEMO=off runs every test; a copy of this folder on its own has no memo and runs every test.
_MEMO = Path(__file__).resolve().parents[2] / "tools" / "memo_pytest.py"
_memo_pytest = None
if _MEMO.is_file():
    _spec = importlib.util.spec_from_file_location("memo_pytest", _MEMO)
    _memo_pytest = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_memo_pytest)


def pytest_configure(config):
    if _memo_pytest is not None:
        _memo_pytest.pytest_configure(config)
