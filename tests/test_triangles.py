# tests/test_triangles.py — validate triangle witness search
import pytest
from fractions import Fraction
from src.scan_triangles import search_direct, search_curve_points, find_witness


class TestSearchDirect:
    def test_n5(self):
        """n=5: classic 20/3, 3/2, 41/6 triangle."""
        tri = search_direct(5, denom_bound=20)
        assert tri is not None
        assert tri["area"] == 5
        assert tri["a"] ** 2 + tri["b"] ** 2 == tri["c"] ** 2

    def test_n6(self):
        """n=6: 3,4,5 triangle has area 6."""
        tri = search_direct(6, denom_bound=10)
        assert tri is not None
        assert tri["area"] == 6

    def test_n1_no_witness(self):
        """n=1 is not congruent; should find nothing in small search."""
        tri = search_direct(1, denom_bound=50)
        assert tri is None


class TestSearchCurvePoints:
    def test_n5(self):
        tri = search_curve_points(5, height_bound=20)
        assert tri is not None
        assert tri["area"] == 5

    def test_n6(self):
        tri = search_curve_points(6, height_bound=20)
        assert tri is not None
        assert tri["area"] == 6


class TestFindWitness:
    @pytest.mark.parametrize("n", [5, 6, 7, 13, 14, 15, 21, 22])
    def test_small_congruent(self, n):
        """Find witnesses for small known congruent numbers."""
        tri = find_witness(n, denom_bound=200, height_bound=200)
        assert tri is not None, f"No witness found for n={n}"
        assert tri["area"] == n
