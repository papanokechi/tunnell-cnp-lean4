# tests/test_env.py — verify environment can import all dependencies
import pytest


def test_mpmath():
    import mpmath
    assert hasattr(mpmath, "pslq")


def test_sympy():
    import sympy
    assert hasattr(sympy, "isprime")


def test_cypari2_optional():
    """cypari2 is optional; just record whether it's available."""
    try:
        import cypari2
        pari = cypari2.Pari()
        assert pari is not None
    except ImportError:
        pytest.skip("cypari2 not installed (optional)")
