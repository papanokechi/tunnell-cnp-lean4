# src/counts.py — Tunnell-theorem counting routines
"""
Tunnell's theorem (1983) relates congruent-number status to representation
counts by ternary quadratic forms.

For *odd* squarefree n:
    A_n = #{(x,y,z) in Z^3 : 2x^2 + y^2 + 8z^2 = n}
    B_n = #{(x,y,z) in Z^3 : 2x^2 + y^2 + 32z^2 = n}
    n is congruent  <=>  A_n = 2*B_n   (conditional on BSD)

For *even* squarefree n, write m = n/2:
    A_n = #{(x,y,z) in Z^3 : 4x^2 + y^2 + 8z^2 = m}
    B_n = #{(x,y,z) in Z^3 : 4x^2 + y^2 + 32z^2 = m}
    n is congruent  <=>  A_n = 2*B_n   (conditional on BSD)

One direction (congruent => A=2B) is unconditional.
The reverse requires BSD.
"""

from __future__ import annotations
import math
from typing import Tuple


def is_squarefree(n: int) -> bool:
    """Return True if n has no repeated prime factor."""
    if n <= 0:
        return False
    if n == 1:
        return True
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1 if d == 2 else 2
    return True


def squarefree_part(n: int) -> int:
    """Return the largest squarefree divisor d such that n/d is a perfect square."""
    if n <= 0:
        raise ValueError("n must be positive")
    d = 1
    result = n
    p = 2
    while p * p <= result:
        while result % (p * p) == 0:
            result //= (p * p)
        p += 1 if p == 2 else 2
    return result


def _count_representations(a_coeff: int, b_coeff: int, c_coeff: int, target: int) -> int:
    """
    Count #{(x,y,z) in Z^3 : a*x^2 + b*y^2 + c*z^2 = target}.
    Brute-force enumeration; adequate for target <= ~10000.
    """
    if target < 0:
        return 0
    if target == 0:
        return 1  # only (0,0,0)

    count = 0
    # bounds: |x| <= sqrt(target / a_coeff), etc.
    x_bound = math.isqrt(target // a_coeff)
    for x in range(-x_bound, x_bound + 1):
        rem1 = target - a_coeff * x * x
        if rem1 < 0:
            continue
        y_bound = math.isqrt(rem1 // b_coeff)
        for y in range(-y_bound, y_bound + 1):
            rem2 = rem1 - b_coeff * y * y
            if rem2 < 0:
                continue
            if rem2 % c_coeff != 0:
                continue
            q = rem2 // c_coeff
            z_sq = q
            if z_sq < 0:
                continue
            z_int = math.isqrt(z_sq)
            if z_int * z_int == z_sq:
                # z = +z_int and z = -z_int (unless z_int == 0)
                count += 1 if z_int == 0 else 2
    return count


def count_tunnell_forms(n: int) -> Tuple[int, int]:
    """
    Compute (A_n, B_n) for Tunnell's theorem.

    Returns (A_n, B_n) where n is congruent iff A_n == 2*B_n
    (unconditional in one direction; reverse conditional on BSD).

    Raises ValueError if n is not a positive squarefree integer.
    """
    if n <= 0:
        raise ValueError(f"n must be positive, got {n}")
    if not is_squarefree(n):
        raise ValueError(f"n={n} is not squarefree")

    if n % 2 == 1:
        # odd case: forms 2x^2 + y^2 + 8z^2 and 2x^2 + y^2 + 32z^2
        A = _count_representations(2, 1, 8, n)
        B = _count_representations(2, 1, 32, n)
    else:
        # even case: use m = n // 2; forms 4x^2 + y^2 + 8z^2 and 4x^2 + y^2 + 32z^2
        m = n // 2
        A = _count_representations(4, 1, 8, m)
        B = _count_representations(4, 1, 32, m)
    return (A, B)


def is_congruent_tunnell(n: int) -> bool:
    """
    Test if n is a congruent number via Tunnell's criterion.

    WARNING: the direction "A_n == 2*B_n => n congruent" is
    CONDITIONAL ON BSD.  This function returns the predicted status.
    """
    A, B = count_tunnell_forms(n)
    return A == 2 * B


# --- Known congruent numbers for validation ---
# First congruent numbers (OEIS A003273):
# 5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31, 34, 37, 38, 39, 41, 46, 47, ...
KNOWN_CONGRUENT_SMALL = {
    5, 6, 7, 13, 14, 15, 21, 22, 23, 29, 30, 31, 34, 37, 38, 39,
    41, 46, 47, 53, 55, 62, 65, 69, 70, 71, 77, 78, 79, 85, 86, 87,
    93, 94, 95, 101, 102, 103, 109, 110, 111, 118, 119,
}
# Known NON-congruent squarefree numbers:
KNOWN_NON_CONGRUENT_SMALL = {1, 2, 3, 10, 11, 17, 19, 26, 33, 35, 43}
