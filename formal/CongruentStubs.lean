/-
  Congruent.lean — Formal specification for Tunnell decision tree.

  Layer 1 (this file): structural spec matching the Python implementation.
  Layer 2 (RepCount section): Finset-based definition of representation
    counting with provable properties.

  Mirrors:
    _count_representations(a, b, c, target) -> Int
    count_tunnell_forms(n) -> (A, B)       [odd/even branch]
    is_congruent_tunnell(n) -> A == 2*B

  Status: zero sorry, zero axioms.
-/

namespace Congruent

/-! ### Squarefree predicate (matches Python `is_squarefree`) -/

def IsSquarefree (n : Nat) : Prop :=
  n > 0 ∧ ∀ d : Nat, d > 1 → ¬(d * d ∣ n)

/-! ## Representation counting — formal spec

The Python `_count_representations(a, b, c, target)` computes
  #{(x,y,z) ∈ ℤ³ : a·x² + b·y² + c·z² = target}
by brute-force enumeration over |x| ≤ √(target/a), etc.

We specify this as the cardinality of a Finset of integer triples.
The definition is constructive and decidable for any concrete inputs.
-/

/--
The solution set for the ternary quadratic form a·x² + b·y² + c·z² = t.
Given a search bound B, this is the finite set of all (x,y,z) with
|x|,|y|,|z| ≤ B satisfying the equation.

For correctness, B must be chosen large enough: B ≥ √(t / min(a,b,c)).
The Python code derives exact bounds per variable from the target.
-/
def solSet (a b c t : Int) (B : Nat) : Finset (Int × Int × Int) :=
  let range := Finset.Icc (-(B : Int)) (B : Int)
  (range ×ˢ range ×ˢ range).filter fun ⟨x, y, z⟩ =>
    a * x * x + b * y * y + c * z * z = t

/--
repCount: cardinality of the solution set within a sufficient bound.

For positive-definite forms (a,b,c > 0) with target t ≥ 0, any
B ≥ √(t) is sufficient since a·x² ≤ t implies |x| ≤ √(t/a) ≤ √t.
We use B = t.natAbs as a safe (generous) upper bound.

Matches Python `_count_representations(a, b, c, target)`.
-/
def repCount (a b c target : Int) : Int :=
  if target < 0 then 0
  else (solSet a b c target target.natAbs).card

/-! ### Properties of repCount (all provable from the definition) -/

/--
Negative targets have no representations.
Matches Python: `if target < 0: return 0`.
-/
theorem repCount_neg {a b c t : Int} (h : t < 0) :
    repCount a b c t = 0 := by
  simp [repCount, h, show ¬(t < 0 → False) from fun f => f h]
  split <;> simp_all

/--
repCount is always non-negative.
(It's a cardinality cast to Int, so this is immediate.)
-/
theorem repCount_nonneg (a b c t : Int) :
    repCount a b c t ≥ 0 := by
  simp [repCount]
  split
  · exact le_refl 0
  · exact Int.natCast_nonneg _

/--
Coordinate negation symmetry: if (x,y,z) is a solution then so is (-x,y,z).
This is the foundation for the Python code's sign-aware counting
(`count += 1 if z_int == 0 else 2`).

Statement: the map (x,y,z) ↦ (-x,y,z) sends solutions to solutions.
-/
theorem solSet_neg_x {a b c t : Int} {B : Nat} {x y z : Int}
    (hmem : (x, y, z) ∈ solSet a b c t B)
    (hx : (-x).natAbs ≤ B) :
    (-x, y, z) ∈ solSet a b c t B := by
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem ⊢
  constructor
  · constructor
    · constructor
      · omega
      · omega
    · exact hmem.1.2
  · linarith [hmem.2]

/--
Similarly for y-negation.
-/
theorem solSet_neg_y {a b c t : Int} {B : Nat} {x y z : Int}
    (hmem : (x, y, z) ∈ solSet a b c t B)
    (hy : (-y).natAbs ≤ B) :
    (x, -y, z) ∈ solSet a b c t B := by
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem ⊢
  constructor
  · constructor
    · exact hmem.1.1
    · constructor
      · constructor <;> omega
      · exact hmem.1.2.2
  · linarith [hmem.2]

/--
Similarly for z-negation.
-/
theorem solSet_neg_z {a b c t : Int} {B : Nat} {x y z : Int}
    (hmem : (x, y, z) ∈ solSet a b c t B)
    (hz : (-z).natAbs ≤ B) :
    (x, y, -z) ∈ solSet a b c t B := by
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem ⊢
  constructor
  · constructor
    · exact hmem.1.1
    · constructor
      · exact hmem.1.2.1
      · constructor <;> omega
  · linarith [hmem.2]

/-! ## Strengthened invariants -/

/-! ### 1. Monotonicity and independence of bound

Key insight: enlarging the search cube can only add solutions, never remove them.
Once the cube is large enough to contain all solutions, the count stabilizes.

For positive-definite forms with a,b,c > 0 and t ≥ 0:
  any solution (x,y,z) satisfies |x| ≤ √(t/a), |y| ≤ √(t/b), |z| ≤ √(t/c).
So taking B ≥ t suffices (since a,b,c ≥ 1 for our forms).
-/

/--
Monotonicity: if B₁ ≤ B₂, every solution in the smaller cube is in the larger.
-/
theorem solSet_mono {a b c t : Int} {B₁ B₂ : Nat} (h : B₁ ≤ B₂) :
    solSet a b c t B₁ ⊆ solSet a b c t B₂ := by
  intro ⟨x, y, z⟩ hmem
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem ⊢
  constructor
  · constructor
    · constructor <;> [linarith [hmem.1.1.1]; linarith [hmem.1.1.2]]
    · constructor
      · constructor <;> [linarith [hmem.1.2.1.1]; linarith [hmem.1.2.1.2]]
      · constructor <;> [linarith [hmem.1.2.2.1]; linarith [hmem.1.2.2.2]]
  · exact hmem.2

/--
Monotonicity for cardinality: enlarging the bound cannot decrease the count.
-/
theorem solSet_card_mono {a b c t : Int} {B₁ B₂ : Nat} (h : B₁ ≤ B₂) :
    (solSet a b c t B₁).card ≤ (solSet a b c t B₂).card :=
  Finset.card_le_card (solSet_mono h)

/--
Coordinate bound for positive-definite forms:
if a > 0 and a*x² is part of a sum equaling t ≥ 0, then |x| ≤ t.
(Sharper bound: |x| ≤ √(t/a), but t suffices and is simpler to state.)

This is the key lemma for bound independence.
-/
theorem coord_bound_of_sum_eq {a val t : Int}
    (ha : a > 0) (hval : a * val * val ≤ t) (ht : t ≥ 0) :
    val.natAbs ≤ t.natAbs := by
  by_contra h_gt
  push_neg at h_gt
  -- If |val| > t.natAbs, then val² > t² ≥ t (for t ≥ 0),
  -- so a*val² ≥ val² > t, contradicting a*val*val ≤ t.
  -- We show val*val > t, giving a*val*val ≥ val*val > t.
  have hv_abs : val.natAbs > t.natAbs := h_gt
  have hv_sq : val * val ≥ (t.natAbs + 1) * (t.natAbs + 1) := by
    have : (val.natAbs : Int) ≥ t.natAbs + 1 := by omega
    calc val * val = (val.natAbs : Int) * (val.natAbs : Int) := by
            simp [Int.natAbs_mul_self']
         _ ≥ (t.natAbs + 1) * (t.natAbs + 1) := by nlinarith
  have : (t.natAbs : Int) + 1 > 0 := by omega
  have : (t.natAbs + 1 : Int) * (t.natAbs + 1) > t := by nlinarith [Int.natAbs_eq t, ht]
  linarith [mul_le_mul_of_nonneg_left (le_refl (val * val)) (le_of_lt ha)]

/--
Any solution in solSet with positive-definite coefficients has all
coordinates bounded by t.natAbs. This means B = t.natAbs is sufficient.
-/
theorem solSet_sufficient_bound {a b c t : Int} {B : Nat} {x y z : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hmem : (x, y, z) ∈ solSet a b c t B) :
    x.natAbs ≤ t.natAbs ∧ y.natAbs ≤ t.natAbs ∧ z.natAbs ≤ t.natAbs := by
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
  have heq := hmem.2
  -- From a*x² + b*y² + c*z² = t with a,b,c > 0:
  -- a*x² ≤ t, b*y² ≤ t, c*z² ≤ t
  have hx_sq : a * x * x ≤ t := by nlinarith [sq_nonneg y, sq_nonneg z, mul_pos hb (mul_self_nonneg y), mul_pos hc (mul_self_nonneg z)]
  have hy_sq : b * y * y ≤ t := by nlinarith [sq_nonneg x, sq_nonneg z, mul_pos ha (mul_self_nonneg x), mul_pos hc (mul_self_nonneg z)]
  have hz_sq : c * z * z ≤ t := by nlinarith [sq_nonneg x, sq_nonneg y, mul_pos ha (mul_self_nonneg x), mul_pos hb (mul_self_nonneg y)]
  exact ⟨coord_bound_of_sum_eq ha hx_sq ht,
         coord_bound_of_sum_eq hb hy_sq ht,
         coord_bound_of_sum_eq hc hz_sq ht⟩

/--
**Independence of bound (stability):**
For positive-definite forms with t ≥ 0, any B ≥ t.natAbs gives the same count.
This is the central theorem: `repCount` is well-defined regardless of the specific
bound, as long as it's large enough.
-/
theorem solSet_stable {a b c t : Int} {B : Nat}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B) :
    solSet a b c t B = solSet a b c t t.natAbs := by
  ext ⟨x, y, z⟩
  constructor
  · intro hmem
    have ⟨hx, hy, hz⟩ := solSet_sufficient_bound ha hb hc ht hmem
    simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem ⊢
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hmem.2⟩
  · intro hmem
    exact solSet_mono hB hmem

/--
Corollary: for positive-definite forms, the count at any sufficient bound
equals the count at the canonical bound t.natAbs.
-/
theorem repCount_stable {a b c t : Int} {B : Nat}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B) :
    (solSet a b c t B).card = (solSet a b c t t.natAbs).card := by
  rw [solSet_stable ha hb hc ht hB]

/-! ### 2. Full sign symmetry

Combine the per-coordinate negation lemmas into a single structure.
For solutions within a sufficient bound, negation of any coordinate
stays within the bound (since |−v| = |v|).
-/

/--
For solutions in a sufficient bound, coordinate negation stays in-bounds.
-/
theorem natAbs_neg_eq (v : Int) : (-v).natAbs = v.natAbs := by
  simp [Int.natAbs_neg]

/--
**Full sign symmetry:** if (x,y,z) solves the form within a sufficient bound,
then all eight sign-flips are also solutions within the same bound.
-/
theorem solSet_sign_symmetry {a b c t : Int} {B : Nat} {x y z : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B)
    (hmem : (x, y, z) ∈ solSet a b c t B) :
    (-x, y, z) ∈ solSet a b c t B ∧
    (x, -y, z) ∈ solSet a b c t B ∧
    (x, y, -z) ∈ solSet a b c t B ∧
    (-x, -y, z) ∈ solSet a b c t B ∧
    (-x, y, -z) ∈ solSet a b c t B ∧
    (x, -y, -z) ∈ solSet a b c t B ∧
    (-x, -y, -z) ∈ solSet a b c t B := by
  have ⟨hxb, hyb, hzb⟩ := solSet_sufficient_bound ha hb hc ht hmem
  -- All negated coordinates have the same natAbs, so they're in-bounds
  have hx_neg : (-x).natAbs ≤ B := by rw [natAbs_neg_eq]; omega
  have hy_neg : (-y).natAbs ≤ B := by rw [natAbs_neg_eq]; omega
  have hz_neg : (-z).natAbs ≤ B := by rw [natAbs_neg_eq]; omega
  -- Build each sign-flip
  have h_nx := solSet_neg_x hmem hx_neg
  have h_ny := solSet_neg_y hmem hy_neg
  have h_nz := solSet_neg_z hmem hz_neg
  have h_nxny := solSet_neg_y h_nx hy_neg
  have h_nxnz := solSet_neg_z h_nx hz_neg
  have h_nynz := solSet_neg_z h_ny hz_neg
  have h_nxnynz := solSet_neg_z h_nxny hz_neg
  exact ⟨h_nx, h_ny, h_nz, h_nxny, h_nxnz, h_nynz, h_nxnynz⟩

/--
**Origin lemma:** (0,0,0) is a solution iff t = 0.
Matches Python: `if target == 0: return 1`.
-/
theorem solSet_origin {a b c t : Int} {B : Nat} (hB : 0 < B) :
    (0, 0, 0) ∈ solSet a b c t B ↔ t = 0 := by
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro ⟨_, h⟩; linarith
  · intro h; refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> omega

/-! ### 3. Unbounded solution set and bridging lemma

Define the "mathematical" solution set (unbounded) and show it agrees
with the bounded version for any sufficient bound.
-/

/--
The unbounded solution set: all integer triples satisfying the form equation.
This is the "mathematical" definition, independent of any search bound.
-/
def solSet∞ (a b c t : Int) : Set (Int × Int × Int) :=
  { p | let (x, y, z) := p; a * x * x + b * y * y + c * z * z = t }

/--
Every bounded solution is an unbounded solution.
-/
theorem solSet_sub_solSet∞ {a b c t : Int} {B : Nat} :
    ↑(solSet a b c t B) ⊆ solSet∞ a b c t := by
  intro ⟨x, y, z⟩ hmem
  simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_coe] at hmem
  exact hmem.2

/--
For positive-definite forms with t ≥ 0, every unbounded solution
has coordinates bounded by t.natAbs.

This is the converse direction: solutions can't escape the cube.
-/
theorem solSet∞_bounded {a b c t : Int} {x y z : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hmem : (x, y, z) ∈ solSet∞ a b c t) :
    x.natAbs ≤ t.natAbs ∧ y.natAbs ≤ t.natAbs ∧ z.natAbs ≤ t.natAbs := by
  simp [solSet∞] at hmem
  have hx_sq : a * x * x ≤ t := by nlinarith [sq_nonneg y, sq_nonneg z, mul_pos hb (mul_self_nonneg y), mul_pos hc (mul_self_nonneg z)]
  have hy_sq : b * y * y ≤ t := by nlinarith [sq_nonneg x, sq_nonneg z, mul_pos ha (mul_self_nonneg x), mul_pos hc (mul_self_nonneg z)]
  have hz_sq : c * z * z ≤ t := by nlinarith [sq_nonneg x, sq_nonneg y, mul_pos ha (mul_self_nonneg x), mul_pos hb (mul_self_nonneg y)]
  exact ⟨coord_bound_of_sum_eq ha hx_sq ht,
         coord_bound_of_sum_eq hb hy_sq ht,
         coord_bound_of_sum_eq hc hz_sq ht⟩

/--
**Finiteness of the unbounded solution set** for positive-definite forms.
Since all solutions are bounded, the "infinite" solution set is actually finite.
-/
theorem solSet∞_finite (a b c t : Int)
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0) :
    Set.Finite (solSet∞ a b c t) := by
  apply Set.Finite.subset (Set.Finite.prod (Set.Finite.Icc (-(t : Int)) t)
    (Set.Finite.prod (Set.Finite.Icc (-(t : Int)) t) (Set.Finite.Icc (-(t : Int)) t)))
  intro ⟨x, y, z⟩ hmem
  have ⟨hx, hy, hz⟩ := solSet∞_bounded ha hb hc ht hmem
  simp [Set.mem_prod, Set.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/--
**Bridging lemma:** the bounded solSet at the canonical bound captures
exactly the unbounded solution set for positive-definite forms.

This is the key correctness property: our computable `repCount` counts
the same solutions as the mathematical definition.
-/
theorem solSet_eq_solSet∞ {a b c t : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0) :
    ↑(solSet a b c t t.natAbs) = solSet∞ a b c t := by
  ext ⟨x, y, z⟩
  constructor
  · exact fun h => solSet_sub_solSet∞ h
  · intro hmem
    have ⟨hx, hy, hz⟩ := solSet∞_bounded ha hb hc ht hmem
    simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_coe]
    simp [solSet∞] at hmem
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hmem⟩ <;> omega

/--
Lean analogue of `count_tunnell_forms` from Python.

Matches the branching structure exactly:
- odd n  → forms (2,1,8) and (2,1,32) with target n
- even n → m = n/2, forms (4,1,8) and (4,1,32) with target m
- returns (A, B)
-/
def tunnellCounts (n : Int) : Int × Int :=
  if n % 2 = 1 then
    let A := repCount 2 1 8 n
    let B := repCount 2 1 32 n
    (A, B)
  else
    let m := n / 2
    let A := repCount 4 1 8 m
    let B := repCount 4 1 32 m
    (A, B)

/-! ### Congruent-number predicate (matches Python `is_congruent_tunnell`) -/

/--
Lean analogue of `is_congruent_tunnell`.

Purely structural: the predicate is exactly A = 2·B.
The implication that this characterizes congruent numbers
is Tunnell's theorem and is NOT stated here.
-/
def isCongruentTunnell (n : Int) : Prop :=
  let (A, B) := tunnellCounts n
  A = 2 * B

/-! ### Structural correctness -/

/--
Structural correctness lemma: `isCongruentTunnell n` is definitionally
equivalent to the equality test used in the Python implementation.

No number theory. No BSD. No analytic assumptions.
Provable by `rfl` — this is a definitional unfolding.
-/
theorem isCongruentTunnell_iff (n : Int) :
    isCongruentTunnell n ↔
      let (A, B) := tunnellCounts n
      A = 2 * B := by
  constructor <;> intro h <;> exact h

/--
Domain guard: non-squarefree n are outside the Tunnell domain.
The Python code raises ValueError for these inputs.
-/
def inTunnellDomain (n : Nat) : Prop :=
  IsSquarefree n

/-! ### Case-split structure (for future provers) -/

/--
The odd/even case split is exhaustive. This witnesses that
`tunnellCounts` covers both branches for any integer.
-/
theorem tunnellCounts_cases (n : Int) :
    (n % 2 = 1 ∧ tunnellCounts n = (repCount 2 1 8 n, repCount 2 1 32 n)) ∨
    (n % 2 ≠ 1 ∧ tunnellCounts n = (repCount 4 1 8 (n/2), repCount 4 1 32 (n/2))) := by
  by_cases h : n % 2 = 1
  · left; exact ⟨h, by simp [tunnellCounts, h]⟩
  · right; exact ⟨h, by simp [tunnellCounts, h]⟩

end Congruent
