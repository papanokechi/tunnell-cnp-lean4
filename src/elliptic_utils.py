# src/elliptic_utils.py — elliptic curve utilities for congruent-number curves
"""
The congruent number curve for n is  E_n : y^2 = x^3 - n^2 x.
This module wraps sympy for basic invariants and optionally uses
cypari2 when available for faster arithmetic.

All functions work with pure-Python fallbacks so the pipeline
runs without cypari2 (just slower for large n).
"""

from __future__ import annotations
import math
from typing import Dict, Any, Optional, Tuple
from fractions import Fraction


def make_curve_coeffs(n: int) -> Tuple[int, int, int, int, int]:
    """
    Return (a1,a2,a3,a4,a6) for E_n: y^2 = x^3 - n^2 x
    in short Weierstrass form  y^2 = x^3 + a4*x + a6.
    """
    return (0, 0, 0, -(n * n), 0)


def discriminant(n: int) -> int:
    """
    Discriminant of E_n: y^2 = x^3 - n^2 x.
    Delta = -16 * (4a^3 + 27b^2) where a = -n^2, b = 0.
    Delta = -16 * 4 * (-n^2)^3 = -16 * 4 * (-n^6) = 64 * n^6.
    """
    return 64 * n ** 6


def j_invariant(n: int) -> Fraction:
    """
    j-invariant of E_n.
    j = -1728 * (4a)^3 / Delta  where a = -n^2.
    j = -1728 * (-4n^2)^3 / (64 n^6) = -1728 * (-64 n^6) / (64 n^6) = 1728.
    All congruent-number curves have j = 1728 (CM by Z[i]).
    """
    return Fraction(1728)


def conductor_naive(n: int) -> int:
    """
    Compute the conductor of E_n naively.
    For E_n: y^2 = x^3 - n^2 x, the conductor is 32 * n^2 when n is
    odd squarefree, with modifications at 2 for even n.

    This is a simplified estimate; exact conductor requires local analysis.
    """
    # For odd squarefree n, conductor = 32 * n^2
    # For n = 2m (m odd squarefree), conductor = 32 * (2m)^2 = 128 * m^2
    # These are upper bounds; actual conductor divides this.
    return 32 * n * n


def torsion_group(n: int) -> str:
    """
    Torsion subgroup of E_n(Q).
    For E_n: y^2 = x^3 - n^2 x, the rational torsion points are:
    O, (0,0), (n,0), (-n,0)  =>  torsion ≅ Z/2 x Z/2.
    """
    return "Z/2 x Z/2"


def rational_torsion_points(n: int) -> list:
    """Return the finite rational torsion points of E_n."""
    return [(0, 0), (n, 0), (-n, 0)]


def compute_invariants(n: int) -> Dict[str, Any]:
    """
    Compute basic invariants of E_n: y^2 = x^3 - n^2 x.
    Returns a dict with discriminant, j-invariant, conductor estimate,
    torsion info, and CM flag.
    """
    return {
        "n": n,
        "model": f"y^2 = x^3 - {n*n}*x",
        "a_invariants": make_curve_coeffs(n),
        "discriminant": discriminant(n),
        "j_invariant": int(j_invariant(n)),
        "conductor_estimate": conductor_naive(n),
        "torsion": torsion_group(n),
        "torsion_points": rational_torsion_points(n),
        "CM": True,
        "CM_discriminant": -4,
    }


def point_on_curve(n: int, x: Fraction, y: Fraction) -> bool:
    """Check if (x, y) lies on E_n: y^2 = x^3 - n^2 x."""
    lhs = y * y
    rhs = x ** 3 - n * n * x
    return lhs == rhs


def curve_to_triangle(n: int, x: Fraction, y: Fraction) -> Optional[Dict[str, Fraction]]:
    """
    Given a rational point (x,y) on E_n with y != 0, recover the
    right triangle with area n.

    The sides are:
      a = |x^2 - n^2| / |y|
      b = 2*n*x / |y|
      c = |x^2 + n^2| / |y|
    """
    if y == 0:
        return None

    x = Fraction(x)
    y = Fraction(y)
    n_f = Fraction(n)

    a = abs(x ** 2 - n_f ** 2) / abs(y)
    b = 2 * n_f * abs(x) / abs(y)
    c = abs(x ** 2 + n_f ** 2) / abs(y)

    # verify: a^2 + b^2 == c^2  and  a*b/2 == n
    assert a * a + b * b == c * c, f"Pythagorean check failed for n={n}"
    assert a * b / 2 == n_f, f"Area check failed for n={n}"

    return {"a": a, "b": b, "c": c, "area": n_f}


# --- Optional cypari2 backend ---
def _try_pari_rank(n: int) -> Optional[int]:
    """Try to compute the algebraic rank of E_n via PARI/GP. Returns None if cypari2 unavailable."""
    try:
        import cypari2
        pari = cypari2.Pari()
        E = pari(f"ellinit([0, 0, 0, -{n*n}, 0])")
        r = pari(f"ellrank({E})")
        # ellrank returns [lower, upper, ...]; take lower bound
        return int(r[0])
    except Exception:
        return None
