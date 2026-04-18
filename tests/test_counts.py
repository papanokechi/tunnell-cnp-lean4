# tests/test_counts.py — validate Tunnell counting against known congruent numbers
import pytest
from src.counts import (
    is_squarefree,
    squarefree_part,
    count_tunnell_forms,
    is_congruent_tunnell,
    _count_representations,
    KNOWN_CONGRUENT_SMALL,
    KNOWN_NON_CONGRUENT_SMALL,
)


class TestSquarefree:
    def test_primes(self):
        for p in [2, 3, 5, 7, 11, 13]:
            assert is_squarefree(p)

    def test_squares(self):
        for n in [4, 8, 9, 12, 16, 18, 25, 27]:
            assert not is_squarefree(n)

    def test_squarefree_composites(self):
        for n in [6, 10, 14, 15, 21, 22, 30]:
            assert is_squarefree(n)

    def test_one(self):
        assert is_squarefree(1)

    def test_nonpositive(self):
        assert not is_squarefree(0)
        assert not is_squarefree(-1)


class TestSquarefreePart:
    def test_basic(self):
        assert squarefree_part(1) == 1
        assert squarefree_part(4) == 1
        assert squarefree_part(12) == 3
        assert squarefree_part(18) == 2
        assert squarefree_part(50) == 2


class TestRepresentationCounts:
    def test_trivial(self):
        assert _count_representations(1, 1, 1, 0) == 1

    def test_sum_of_three_squares_3(self):
        # 1^2 + 1^2 + 1^2 = 3, with sign permutations: 2^3 = 8
        assert _count_representations(1, 1, 1, 3) == 8

    def test_known_form(self):
        # 2*1^2 + 1^2 + 8*0^2 = 3? 2+1+0=3 yes.
        # x=+-1, y=+-1, z=0 => 4 reps
        # x=0, y^2=3 => no. So count = 4
        c = _count_representations(2, 1, 8, 3)
        assert c == 4


class TestTunnellCounts:
    def test_n5_congruent(self):
        """n=5 is the smallest congruent number; Tunnell should confirm."""
        A, B = count_tunnell_forms(5)
        assert A == 2 * B, f"n=5: A={A}, B={B}, expected A=2B"

    def test_n1_not_congruent(self):
        """n=1 is NOT congruent."""
        A, B = count_tunnell_forms(1)
        assert A != 2 * B, f"n=1: A={A}, B={B}, should NOT be A=2B"

    def test_n6_congruent(self):
        A, B = count_tunnell_forms(6)
        assert A == 2 * B

    def test_n7_congruent(self):
        A, B = count_tunnell_forms(7)
        assert A == 2 * B

    def test_n2_not_congruent(self):
        A, B = count_tunnell_forms(2)
        assert A != 2 * B

    def test_n3_not_congruent(self):
        A, B = count_tunnell_forms(3)
        assert A != 2 * B

    def test_not_squarefree_raises(self):
        with pytest.raises(ValueError):
            count_tunnell_forms(4)

    def test_negative_raises(self):
        with pytest.raises(ValueError):
            count_tunnell_forms(-1)


class TestKnownCongruent:
    """Cross-validate Tunnell against the OEIS list for small n."""

    @pytest.mark.parametrize("n", sorted(KNOWN_CONGRUENT_SMALL))
    def test_known_congruent(self, n):
        assert is_congruent_tunnell(n), f"n={n} should be congruent"

    @pytest.mark.parametrize("n", sorted(KNOWN_NON_CONGRUENT_SMALL))
    def test_known_non_congruent(self, n):
        if not is_squarefree(n):
            pytest.skip(f"n={n} is not squarefree")
        assert not is_congruent_tunnell(n), f"n={n} should NOT be congruent"
