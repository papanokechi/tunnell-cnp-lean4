/-
  Congruent.lean — Formal specification for Tunnell decision tree.

  Layer 1: structural spec matching the Python implementation.
  Layer 2: Finset-based repCount with provable properties.
  Layer 3: bound independence, full sign symmetry, unbounded bridge.
  Layer 4: orbit pairing / evenness, theta series, Tunnell axiom (BSD).

  Depends on: Mathlib4 (Finset, Set, Int, Rat, standard algebra).

  Mirrors:
    _count_representations(a, b, c, target) -> Int
    count_tunnell_forms(n) -> (A, B)       [odd/even branch]
    is_congruent_tunnell(n) -> A == 2*B

  ──────────────────────────────────────────────────────────────
  FILE TOUR (§§ 1–6)
  ──────────────────────────────────────────────────────────────

  §1 Foundations (lines ~55–100)
     IsSquarefree, solSet, repCount — core definitions mirroring
     Python's _count_representations and is_squarefree.

  §2 Basic properties (lines ~100–160)
     repCount_neg, repCount_nonneg, solSet_neg_x/y/z —
     coordinate-negation symmetry (per-axis).

  §3 Strengthened invariants (lines ~160–470)
     3a. Monotonicity & bound independence:
         solSet_mono → solSet_stable → repCount_stable.
         Key insight: solutions are bounded by |t| for pos-def forms.
     3b. Full sign symmetry:
         solSet_sign_symmetry (all 8 sign-flips in one lemma).
         solSet_origin (0,0,0 ↔ t=0).
     3c. Unbounded bridge:
         solSet∞ (mathematical definition) ↔ solSet at canonical bound.
         solSet∞_finite, solSet_eq_solSet∞.

  §4 Orbit pairing & evenness (lines ~470–680)
     Generic Finset involution lemma (card_even_of_involution).
     negTriple involution on solSetNZ → nonzero count is even.
     repCount_parity_split, repCount_even_of_pos.

  Tunnell counting defs (lines ~680–740)
     tunnellCounts, isCongruentTunnell, tunnellCounts_cases.
     Placed here so §5 and §6 can reference them.

  §5 Theta series (lines ~740–840)
     thetaCoeff := repCount (combinatorial alias).
     thetaCoeff_eq_solSet∞_card — connects to mathematical set.
     tunnellThetaCoeffs_eq_tunnellCounts.

  §6 Tunnell's theorem (lines ~840–end)
     IsCongruentNumber, OnCurveEn.
     AlgebraicRank, AnalyticRank (opaque), BSD_for (meaningful Prop).
     tunnell_conditional_on_BSD (single axiom).
     tunnell_forward, tunnell_reverse_under_BSD.

  Status: zero sorry, 1 axiom (tunnell_conditional_on_BSD).
          2 opaque defs (AlgebraicRank, AnalyticRank).
  ──────────────────────────────────────────────────────────────
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
  simp [repCount, h]

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

/-! ### 4. Orbit pairing and evenness of nonzero contributions

For a positive-definite form, the sign-flip map v ↦ −v is an involution
on the solution set. Every nonzero solution v has v ≠ −v, so nonzero
solutions pair up, making the count of nonzero solutions even.
-/

/--
**Negation closure on the canonical solution set:**
if (x,y,z) ∈ solSet then (−x,−y,−z) ∈ solSet.
Wraps `solSet_sign_symmetry` for the full-negation case.
-/
theorem solSet_neg_closed {a b c t : Int} {B : Nat} {x y z : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B)
    (hmem : (x, y, z) ∈ solSet a b c t B) :
    (-x, -y, -z) ∈ solSet a b c t B :=
  (solSet_sign_symmetry ha hb hc ht hB hmem).2.2.2.2.2.2

/--
**Negation injectivity:** if v ≠ (0,0,0) then v ≠ −v.
This is the key fact that makes nonzero orbits have size exactly 2.
-/
theorem neg_ne_self_of_ne_zero {x y z : Int}
    (hne : (x, y, z) ≠ (0, 0, 0)) :
    (x, y, z) ≠ (-x, -y, -z) := by
  intro heq
  apply hne
  have hx : x = -x := congrArg (·.1) heq
  have hyz : (y, z) = (-y, -z) := congrArg (·.2) heq
  have hy : y = -y := congrArg (·.1) hyz
  have hz : z = -z := congrArg (·.2) hyz
  have : x = 0 := by omega
  have : y = 0 := by omega
  have : z = 0 := by omega
  simp_all

/--
**Orbit pair membership:** if v is a nonzero solution, then both v and −v
are distinct members of the solution set.
-/
theorem orbit_pair_distinct {a b c t : Int} {B : Nat} {x y z : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B)
    (hmem : (x, y, z) ∈ solSet a b c t B)
    (hne : (x, y, z) ≠ (0, 0, 0)) :
    (-x, -y, -z) ∈ solSet a b c t B ∧ (x, y, z) ≠ (-x, -y, -z) :=
  ⟨solSet_neg_closed ha hb hc ht hB hmem, neg_ne_self_of_ne_zero hne⟩

/--
The negation map on ℤ³ triples.
-/
def negTriple (v : Int × Int × Int) : Int × Int × Int :=
  (-v.1, -v.2.1, -v.2.2)

/--
negTriple is an involution: applying it twice gives the original.
-/
theorem negTriple_involution (v : Int × Int × Int) :
    negTriple (negTriple v) = v := by
  simp [negTriple]

/--
negTriple has no nonzero fixed points.
-/
theorem negTriple_no_nonzero_fixpoint {v : Int × Int × Int}
    (hne : v ≠ (0, 0, 0)) : negTriple v ≠ v := by
  obtain ⟨x, y, z⟩ := v
  simp [negTriple]
  exact fun heq => neg_ne_self_of_ne_zero hne (by rw [heq])

/--
negTriple preserves membership in the solution set (for positive-definite forms).
-/
theorem negTriple_mem_solSet {a b c t : Int} {B : Nat} {v : Int × Int × Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B)
    (hmem : v ∈ solSet a b c t B) :
    negTriple v ∈ solSet a b c t B := by
  obtain ⟨x, y, z⟩ := v
  exact solSet_neg_closed ha hb hc ht hB hmem

/--
The nonzero solution set: solutions excluding the origin.
-/
def solSetNZ (a b c t : Int) (B : Nat) : Finset (Int × Int × Int) :=
  (solSet a b c t B).filter fun v => v ≠ (0, 0, 0)

/-! #### Generic Finset involution lemma

A Finset equipped with a fixed-point-free involution has even cardinality.
We prove this by strong induction on the set's cardinality:
  - If the set is empty, card = 0 which is even.
  - Otherwise pick any element x. Its partner f(x) ≠ x is also in s.
    Remove both; by induction the remainder has even card, so the whole
    set has card = remainder.card + 2 which is even.

This is the missing piece that closes the orbit-pairing sorry's.
-/

/--
**Fixed-point-free involution ⇒ even cardinality.**

Given a Finset s with a function f such that:
  1. f maps s into s,
  2. f is an involution (f(f(x)) = x),
  3. f has no fixed points in s,
then s has even cardinality.
-/
theorem card_even_of_involution [DecidableEq α]
    (s : Finset α) (f : α → α)
    (hf_mem : ∀ x ∈ s, f x ∈ s)
    (hf_inv : ∀ x ∈ s, f (f x) = x)
    (hf_fix : ∀ x ∈ s, f x ≠ x) :
    Even s.card := by
  -- Proof by strong induction on s.card
  induction s using Finset.strongInduction with
  | ind s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    · -- s is nonempty: pick an element x
      obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hs
      -- f x ∈ s and f x ≠ x
      have hfx := hf_mem x hx
      have hne := hf_fix x hx
      -- Remove both x and f x from s
      let s' := s.erase x |>.erase (f x)
      -- s' is strictly smaller
      have hs'_sub : s' ⊂ s := by
        apply Finset.ssubset_of_subset_of_ne
        · intro a ha
          simp [s', Finset.mem_erase] at ha
          exact ha.1.2
        · intro heq
          have : x ∈ s' := heq ▸ hx
          simp [s', Finset.mem_erase] at this
      -- The involution restricts to s': if y ∈ s' then f y ∈ s'
      have hf_mem' : ∀ y ∈ s', f y ∈ s' := by
        intro y hy
        simp [s', Finset.mem_erase] at hy ⊢
        have hy_s := hy.1.2
        constructor
        · constructor
          · -- f y ≠ f x: if f y = f x then y = f(f y) = f(f x) = x, contradiction
            intro h
            have := hy.1.1  -- y ≠ f x
            have : y = x := by
              calc y = f (f y) := (hf_inv y hy_s).symm
                   _ = f (f x) := by rw [h]
                   _ = x := hf_inv x hx
            exact hy.2 this
          · exact hf_mem y hy_s
        · -- f y ≠ x: if f y = x then y = f(f y) = f x, contradiction
          intro h
          have : y = f x := by
            calc y = f (f y) := (hf_inv y hy_s).symm
                 _ = f x := by rw [h]
          exact hy.1.1 this
      -- Involution and fixed-point-free properties transfer to s'
      have hf_inv' : ∀ y ∈ s', f (f y) = y := fun y hy => by
        simp [s', Finset.mem_erase] at hy; exact hf_inv y hy.1.2
      have hf_fix' : ∀ y ∈ s', f y ≠ y := fun y hy => by
        simp [s', Finset.mem_erase] at hy; exact hf_fix y hy.1.2
      -- By induction, s' has even cardinality
      have heven' := ih s' hs'_sub f hf_mem' hf_inv' hf_fix'
      -- s.card = s'.card + 2
      have hcard : s.card = s'.card + 2 := by
        have h1 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
        have hfx_in_erase : f x ∈ s.erase x := by
          simp [Finset.mem_erase]; exact ⟨hne.symm, hfx⟩
        have h2 : s'.card = (s.erase x).card - 1 :=
          Finset.card_erase_of_mem hfx_in_erase
        have hcard_pos : s.card ≥ 1 := Finset.one_le_card.mpr ⟨x, hx⟩
        have hcard_pos2 : (s.erase x).card ≥ 1 :=
          Finset.one_le_card.mpr ⟨f x, hfx_in_erase⟩
        omega
      rw [hcard]
      exact Even.add_two heven'

/--
**Nonzero solution count is even:**
The involution v ↦ −v pairs up all nonzero solutions (since v ≠ −v for v ≠ 0),
so the count of nonzero solutions is always even.

This is the formal version of the Python optimization
`count += 1 if z_int == 0 else 2` for positive coordinates.
-/
theorem solSetNZ_card_even {a b c t : Int} {B : Nat}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0)
    (hB : t.natAbs ≤ B) :
    2 ∣ (solSetNZ a b c t B).card := by
  -- Apply the generic involution lemma with negTriple
  have heven := card_even_of_involution (solSetNZ a b c t B) negTriple
    -- 1. negTriple maps solSetNZ into solSetNZ
    (fun v hv => by
      simp [solSetNZ, Finset.mem_filter] at hv ⊢
      constructor
      · exact negTriple_mem_solSet ha hb hc ht hB hv.1
      · intro heq
        apply hv.2
        have := negTriple_involution v
        rw [heq] at this
        simp [negTriple] at this
        obtain ⟨x, y, z⟩ := v
        simp [negTriple] at heq
        ext <;> omega)
    -- 2. negTriple is an involution
    (fun v hv => by
      simp [solSetNZ, Finset.mem_filter] at hv
      exact negTriple_involution v)
    -- 3. negTriple has no fixed points (all elements are nonzero)
    (fun v hv => by
      simp [solSetNZ, Finset.mem_filter] at hv
      exact negTriple_no_nonzero_fixpoint hv.2)
  exact even_iff_two_dvd.mp heven

/--
**Total representation count parity:**
repCount = |solSetNZ| + (if origin ∈ solSet then 1 else 0).
When t > 0, the origin is not a solution, so repCount = |solSetNZ| which is even.
When t = 0, repCount = |solSetNZ| + 1 = 0 + 1 = 1 (the origin is the only solution).
-/
theorem repCount_parity_split {a b c t : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t ≥ 0) :
    repCount a b c t =
      (solSetNZ a b c t t.natAbs).card +
      if (0, 0, 0) ∈ solSet a b c t t.natAbs then 1 else 0 := by
  simp [repCount]
  split
  · omega
  · rename_i h_not_neg
    push_neg at h_not_neg
    -- solSet = solSetNZ ∪ (solSet ∩ {origin}), these are disjoint
    -- We use Finset.filter_card_add_filter_neg_card_eq_card
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (solSet a b c t t.natAbs) (fun v => v ≠ (0, 0, 0))
    -- The "positive" filter is solSetNZ
    -- The "negative" filter is {v ∈ solSet | v = (0,0,0)} which has card 0 or 1
    simp [solSetNZ] at hsplit
    -- Rewrite: solSet.card = solSetNZ.card + (solSet.filter (· = (0,0,0))).card
    have : (solSet a b c t t.natAbs).card =
        (solSetNZ a b c t t.natAbs).card +
        ((solSet a b c t t.natAbs).filter fun v => v = (0, 0, 0)).card := by
      omega
    rw [this]
    congr 1
    -- The filter for equality to origin has card 1 if origin ∈ solSet, else 0
    by_cases h : (0, 0, 0) ∈ solSet a b c t t.natAbs
    · simp [h]
      have : (solSet a b c t t.natAbs).filter (fun v => v = (0, 0, 0)) = {(0, 0, 0)} := by
        ext v; simp [Finset.mem_filter]; constructor
        · intro ⟨_, hv⟩; exact hv
        · intro hv; exact ⟨hv ▸ h, hv⟩
      rw [this]; simp
    · simp [h]
      have : (solSet a b c t t.natAbs).filter (fun v => v = (0, 0, 0)) = ∅ := by
        ext v; simp [Finset.mem_filter]; intro _ hv; exact h (hv ▸ by assumption)
      rw [this]; simp

/--
Corollary: for t > 0 with positive-definite coefficients, repCount is even.
This is the key arithmetic property used in Tunnell's criterion.
-/
theorem repCount_even_of_pos {a b c t : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (ht : t > 0) :
    2 ∣ repCount a b c t := by
  have ht' : t ≥ 0 := le_of_lt ht
  rw [repCount_parity_split ha hb hc ht']
  -- Origin is not a solution when t > 0
  have hno_origin : (0, 0, 0) ∉ solSet a b c t t.natAbs := by
    intro hmem
    have := (solSet_origin (by omega : (0 : Nat) < t.natAbs)).mp hmem
    omega
  simp [hno_origin]
  exact solSetNZ_card_even ha hb hc ht' (le_refl _)

/-! ### Tunnell counting definitions

These must appear before §5 (theta series) and §6 (Tunnell axiom),
since both reference tunnellCounts and isCongruentTunnell.
-/

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

/--
Lean analogue of `is_congruent_tunnell`.

Purely structural: the predicate is exactly A = 2·B.
The implication that this characterizes congruent numbers
is Tunnell's theorem and is NOT stated here.
-/
def isCongruentTunnell (n : Int) : Prop :=
  let (A, B) := tunnellCounts n
  A = 2 * B

/--
Structural correctness lemma: `isCongruentTunnell n` is definitionally
equivalent to the equality test used in the Python implementation.
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

/-! ### 5. Theta series coefficients

The theta series of a ternary quadratic form Q(x,y,z) = ax² + by² + cz²
is defined as Θ_Q(q) = Σ_{v ∈ ℤ³} q^{Q(v)}.

The coefficient of q^n in Θ_Q counts exactly the number of integer
solutions to Q(v) = n, which is our `repCount`.
-/

/--
The theta coefficient: number of representations of n by the form Q.
This is the combinatorial definition, equivalent to our `repCount`
at the canonical bound.

For positive-definite forms with a,b,c > 0 and n ≥ 0:
  θ_Q(n) := #{(x,y,z) ∈ ℤ³ : ax² + by² + cz² = n}
-/
def thetaCoeff (a b c n : Int) : Int :=
  repCount a b c n

/--
**Theta coefficient equals repCount:** by definition, the theta series
coefficient for q^n is exactly the representation count.

This is trivially true by our definition, but serves as the API entry
point for connecting to modular form theory.
-/
theorem thetaCoeff_eq_repCount (a b c n : Int) :
    thetaCoeff a b c n = repCount a b c n := by
  rfl

/--
Theta coefficient is non-negative.
-/
theorem thetaCoeff_nonneg (a b c n : Int) :
    thetaCoeff a b c n ≥ 0 := by
  simp [thetaCoeff]; exact repCount_nonneg a b c n

/--
Theta coefficient of negative n is zero.
-/
theorem thetaCoeff_neg {a b c n : Int} (h : n < 0) :
    thetaCoeff a b c n = 0 := by
  simp [thetaCoeff]; exact repCount_neg h

/--
**Theta coefficient counts unbounded solutions:**
For positive-definite forms, the theta coefficient equals the cardinality
of the unbounded solution set solSet∞.

This connects the computable definition to the mathematical one.
-/
theorem thetaCoeff_eq_solSet∞_card {a b c n : Int}
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (hn : n ≥ 0) :
    thetaCoeff a b c n =
      (solSet∞_finite a b c n ha hb hc hn).toFinset.card := by
  simp [thetaCoeff, repCount, show ¬(n < 0) by omega]
  -- Both count the same set: solSet at canonical bound = solSet∞
  congr 1
  ext ⟨x, y, z⟩
  simp [Set.Finite.mem_toFinset]
  constructor
  · exact fun h => solSet_sub_solSet∞ (Finset.mem_coe.mpr h)
  · intro hmem
    have ⟨hx, hy, hz⟩ := solSet∞_bounded ha hb hc hn hmem
    simp [solSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    simp [solSet∞] at hmem
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hmem⟩

/--
**Tunnell theta forms:** the specific quadratic forms appearing in Tunnell's theorem.

For odd n:
  Θ₁(q) uses Q₁(x,y,z) = 2x² + y² + 8z²
  Θ₂(q) uses Q₂(x,y,z) = 2x² + y² + 32z²

For even n (with m = n/2):
  Θ₃(q) uses Q₃(x,y,z) = 4x² + y² + 8z²
  Θ₄(q) uses Q₄(x,y,z) = 4x² + y² + 32z²
-/
def tunnellThetaCoeffs (n : Int) : Int × Int :=
  if n % 2 = 1 then
    (thetaCoeff 2 1 8 n, thetaCoeff 2 1 32 n)
  else
    let m := n / 2
    (thetaCoeff 4 1 8 m, thetaCoeff 4 1 32 m)

/--
**Tunnell theta equals tunnellCounts:** the theta series formulation
and the direct counting formulation are identical.
-/
theorem tunnellThetaCoeffs_eq_tunnellCounts (n : Int) :
    tunnellThetaCoeffs n = tunnellCounts n := by
  simp [tunnellThetaCoeffs, tunnellCounts, thetaCoeff]

/-! ### 6. Tunnell's theorem — conditional on BSD

Tunnell's theorem (1983) characterizes congruent numbers in terms
of representation counts of ternary quadratic forms, conditional
on the Birch and Swinnerton-Dyer (BSD) conjecture.

We state this as an axiom with BSD as an explicit hypothesis.
The only axioms in this file appear below.
-/

/--
A positive integer n is a congruent number if there exists a right
triangle with rational sides whose area equals n.
-/
def IsCongruentNumber (n : Nat) : Prop :=
  n > 0 ∧ ∃ (a b c : ℚ), a > 0 ∧ b > 0 ∧ c > 0 ∧
    a * a + b * b = c * c ∧
    a * b / 2 = n

/--
The elliptic curve E_n : y² = x³ − n²x associated to a potential
congruent number n.

We encode this as a predicate on rational points (x, y).
-/
def OnCurveEn (n : Nat) (x y : ℚ) : Prop :=
  y * y = x * x * x - (n : ℚ) * n * x

/-! #### Abstract rank functions

We introduce opaque rank functions to give the BSD axiom a
mathematically meaningful type. These are abstract: their
definitions are irreducible, so nothing can be proved about them
except via the BSD axiom below.

- `AlgebraicRank n`: the Mordell–Weil rank of E_n(ℚ).
- `AnalyticRank n`: the order of vanishing of L(E_n, s) at s = 1.
-/

opaque AlgebraicRank (n : Nat) : Nat
opaque AnalyticRank (n : Nat) : Nat

/--
**BSD hypothesis for E_n:**
The Birch and Swinnerton-Dyer conjecture predicts that the algebraic
rank of E_n equals the analytic rank (order of vanishing of L(E_n, s)
at s = 1).

This is the precise mathematical statement: rank(E_n(ℚ)) = ord_{s=1} L(E_n, s).
It is opaque and non-trivial — no proof or refutation is available in Lean.

For Tunnell's theorem, we specifically need the implication:
  L(E_n, 1) ≠ 0  →  rank(E_n) = 0
which is the Coates–Wiles / Gross–Zagier direction. The converse
(rank 0 → L ≠ 0) is the deep part needed for the full iff.
-/
def BSD_for (n : Nat) : Prop :=
  AlgebraicRank n = AnalyticRank n

/--
**Tunnell's Theorem (1983), conditional on BSD.**

Let n be a positive squarefree integer.

If n is odd:
  n is congruent ↔ #{(x,y,z) ∈ ℤ³ : 2x²+y²+8z² = n}
                   = 2 · #{(x,y,z) ∈ ℤ³ : 2x²+y²+32z² = n}

If n is even (write n = 2m):
  n is congruent ↔ #{(x,y,z) ∈ ℤ³ : 4x²+y²+8z² = m}
                   = 2 · #{(x,y,z) ∈ ℤ³ : 4x²+y²+32z² = m}

The forward direction (congruent → counts equal) is unconditional.
The reverse direction (counts equal → congruent) requires BSD for E_n.

Reference: Tunnell, J.B. "A classical Diophantine problem and
modular forms of weight 3/2." Inventiones mathematicae 72 (1983).
-/
axiom tunnell_conditional_on_BSD :
  ∀ n : Nat, IsSquarefree n →
    -- Forward direction (unconditional):
    (IsCongruentNumber n → isCongruentTunnell n) ∧
    -- Reverse direction (conditional on BSD):
    (BSD_for n → isCongruentTunnell n → IsCongruentNumber n)

/--
**Corollary (forward, unconditional):**
If n is congruent and squarefree, the Tunnell count condition holds.
-/
theorem tunnell_forward (n : Nat) (hsf : IsSquarefree n)
    (hcong : IsCongruentNumber n) :
    isCongruentTunnell n :=
  (tunnell_conditional_on_BSD n hsf).1 hcong

/--
**Corollary (reverse, under BSD):**
If BSD holds and the Tunnell count condition is satisfied for a squarefree n,
then n is a congruent number.
-/
theorem tunnell_reverse_under_BSD (n : Nat) (hsf : IsSquarefree n)
    (hBSD : BSD_for n)
    (htun : isCongruentTunnell n) :
    IsCongruentNumber n :=
  (tunnell_conditional_on_BSD n hsf).2 hBSD htun

end Congruent
