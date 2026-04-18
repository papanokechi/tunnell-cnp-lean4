# src/scan_triangles.py — search for explicit rational right triangle witnesses
"""
If n is a congruent number, there exists a right triangle with rational
sides and area exactly n.  We find witnesses by:

Method 1 (parametric): Enumerate rational points on E_n via the
  parametrization  (x,y) -> triangle.  We search for small-height
  rational points on  y^2 = x^3 - n^2 x  beyond the torsion.

Method 2 (direct): Enumerate candidate legs a = p/q with bounded
  denominator, compute b = 2n/a, check if a^2 + b^2 is a perfect
  square of rationals.
"""

from __future__ import annotations
import math
from fractions import Fraction
from typing import Optional, Dict, List

from src.elliptic_utils import curve_to_triangle, point_on_curve


def _isqrt_exact(n: int) -> Optional[int]:
    """Return sqrt(n) if n is a perfect square, else None."""
    if n < 0:
        return None
    s = math.isqrt(n)
    if s * s == n:
        return s
    return None


def search_direct(n: int, denom_bound: int = 500) -> Optional[Dict[str, Fraction]]:
    """
    Direct search: enumerate legs a = p/q with q <= denom_bound,
    check if b = 2n/a gives a Pythagorean triple.

    Returns dict with sides a, b, c and area, or None.
    """
    n_frac = Fraction(n)
    two_n = 2 * n_frac

    for q in range(1, denom_bound + 1):
        for p in range(1, denom_bound * 4 + 1):
            a = Fraction(p, q)
            b = two_n / a  # b = 2n / a
            # check a^2 + b^2 = c^2 for rational c
            c_sq = a * a + b * b
            # c_sq = num/den; check if num*den is a perfect square? No:
            # c_sq = p_c / q_c; need p_c * q_c ... actually just check
            # if c_sq.numerator and c_sq.denominator are both perfect squares
            num_sq = _isqrt_exact(c_sq.numerator)
            den_sq = _isqrt_exact(c_sq.denominator)
            if num_sq is not None and den_sq is not None:
                c = Fraction(num_sq, den_sq)
                if a > 0 and b > 0 and c > 0:
                    return {"a": a, "b": b, "c": c, "area": n_frac}
    return None


def search_curve_points(n: int, height_bound: int = 1000) -> Optional[Dict[str, Fraction]]:
    """
    Search for non-torsion rational points on E_n: y^2 = x^3 - n^2 x
    by enumerating x = p/q^2 with small p, q and checking if the RHS
    is a perfect square in Q.

    If found, convert to triangle via curve_to_triangle().
    """
    n_sq = n * n
    # Try x = a/b for small a, b
    for b in range(1, height_bound + 1):
        for a in range(-height_bound * 2, height_bound * 2 + 1):
            if a == 0 or a == n or a == -n:
                continue  # skip torsion x-coords
            x = Fraction(a, b)
            rhs = x ** 3 - n_sq * x
            if rhs <= 0:
                continue
            # Check if rhs is a perfect square in Q
            rhs_num = rhs.numerator
            rhs_den = rhs.denominator
            sn = _isqrt_exact(rhs_num)
            sd = _isqrt_exact(rhs_den)
            if sn is not None and sd is not None:
                y = Fraction(sn, sd)
                tri = curve_to_triangle(n, x, y)
                if tri is not None:
                    tri["curve_point"] = (x, y)
                    return tri
    return None


def find_witness(n: int, denom_bound: int = 500, height_bound: int = 500) -> Optional[Dict]:
    """
    Find an explicit rational right triangle with area n.
    Tries curve-point search first (faster for many n), then direct.
    """
    result = search_curve_points(n, height_bound)
    if result is not None:
        return result
    return search_direct(n, denom_bound)


def scan_range(n_start: int, n_end: int,
               denom_bound: int = 500) -> List[Dict]:
    """Scan for triangle witnesses for all squarefree n in range."""
    from src.counts import is_squarefree, is_congruent_tunnell
    results = []
    for n in range(n_start, n_end + 1):
        if not is_squarefree(n):
            continue
        if not is_congruent_tunnell(n):
            continue  # Tunnell says non-congruent; skip
        witness = find_witness(n, denom_bound=denom_bound)
        results.append({
            "n": n,
            "witness_found": witness is not None,
            "witness": {k: str(v) for k, v in witness.items()} if witness else None,
        })
    return results
