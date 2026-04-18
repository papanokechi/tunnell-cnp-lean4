# tests/test_elliptic.py — validate elliptic curve utilities
import pytest
from fractions import Fraction
from src.elliptic_utils import (
    make_curve_coeffs,
    discriminant,
    j_invariant,
    torsion_group,
    rational_torsion_points,
    compute_invariants,
    point_on_curve,
    curve_to_triangle,
)


class TestCurveCoeffs:
    def test_weierstrass(self):
        assert make_curve_coeffs(5) == (0, 0, 0, -25, 0)
        assert make_curve_coeffs(6) == (0, 0, 0, -36, 0)


class TestDiscriminant:
    def test_positive(self):
        for n in [1, 5, 6, 7, 13]:
            assert discriminant(n) == 64 * n ** 6
            assert discriminant(n) > 0


class TestJInvariant:
    def test_always_1728(self):
        for n in range(1, 20):
            assert j_invariant(n) == Fraction(1728)


class TestTorsion:
    def test_structure(self):
        for n in range(1, 20):
            assert torsion_group(n) == "Z/2 x Z/2"

    def test_torsion_points_on_curve(self):
        for n in range(1, 20):
            for x, y in rational_torsion_points(n):
                assert point_on_curve(n, Fraction(x), Fraction(y))


class TestPointOnCurve:
    def test_origin(self):
        assert point_on_curve(5, Fraction(0), Fraction(0))

    def test_known_point_n5(self):
        # E_5: y^2 = x^3 - 25x
        # Known generator: (−4, 6) -> check: 6^2 = 36, (-4)^3 - 25*(-4) = -64+100 = 36. Yes!
        assert point_on_curve(5, Fraction(-4), Fraction(6))

    def test_known_point_n6(self):
        # E_6: y^2 = x^3 - 36x
        # Check (12, 36): 36^2 = 1296, 12^3 - 36*12 = 1728 - 432 = 1296. Yes!
        assert point_on_curve(6, Fraction(12), Fraction(36))


class TestCurveToTriangle:
    def test_n5(self):
        # Point (-4, 6) on E_5
        tri = curve_to_triangle(5, Fraction(-4), Fraction(6))
        assert tri is not None
        assert tri["area"] == 5
        # Verify Pythagorean
        assert tri["a"] ** 2 + tri["b"] ** 2 == tri["c"] ** 2

    def test_n6(self):
        tri = curve_to_triangle(6, Fraction(12), Fraction(36))
        assert tri is not None
        assert tri["area"] == 6

    def test_torsion_returns_none(self):
        assert curve_to_triangle(5, Fraction(0), Fraction(0)) is None


class TestComputeInvariants:
    def test_basic(self):
        inv = compute_invariants(5)
        assert inv["j_invariant"] == 1728
        assert inv["CM"] is True
        assert inv["torsion"] == "Z/2 x Z/2"
