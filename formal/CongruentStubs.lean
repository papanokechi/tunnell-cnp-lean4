/-
  Congruent.lean — Relay-ready structural lemma package for Tunnell decision tree.

  Mirrors the Python implementation exactly:
    _count_representations(a, b, c, target) -> Int
    count_tunnell_forms(n) -> (A, B)       [odd/even branch]
    is_congruent_tunnell(n) -> A == 2*B

  No number theory assumptions. No BSD. No Tunnell theorem.
  Just structural equivalence between the Lean spec and the Python code.

  Next agent can:
    - implement repCount formally (bounded enumeration over ℤ³)
    - axiomatize it with a Finset.card definition
    - prove properties about the quadratic forms
-/

namespace Congruent

/-! ### Squarefree predicate (matches Python `is_squarefree`) -/

def IsSquarefree (n : Nat) : Prop :=
  n > 0 ∧ ∀ d : Nat, d > 1 → ¬(d * d ∣ n)

/-! ### Representation counting interface -/

/--
Interface-level representation-counting function matching the Python
`_count_representations(a, b, c, target)` signature.

Counts #{(x,y,z) ∈ ℤ³ : a·x² + b·y² + c·z² = target}.

We do NOT define the actual counting here — only the interface.
TODO: implement via Finset enumeration or axiomatize.
-/
def repCount (a b c target : Int) : Int := 0  -- placeholder

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
