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

/-! ### Tunnell counting (matches Python `count_tunnell_forms`) -/

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
