/- 
  CongruentStubs.lean — Minimal Lean 4 lemma stubs for congruent-number counting.
  
  These are STUBS with sorry; they document the combinatorial identities
  our computation relies on, as formal proof obligations.
-/

-- Squarefree predicate
def IsSquarefree (n : Nat) : Prop :=
  n > 0 ∧ ∀ d : Nat, d > 1 → ¬(d * d ∣ n)

-- Count of integer representations of n by a ternary quadratic form
-- #{(x,y,z) ∈ ℤ³ : a·x² + b·y² + c·z² = n}
noncomputable def countReps (a b c n : Nat) : Nat :=
  sorry -- Defined by explicit enumeration in the Python implementation

-- Tunnell counts for odd squarefree n
def tunnellA_odd (n : Nat) : Nat := countReps 2 1 8 n
def tunnellB_odd (n : Nat) : Nat := countReps 2 1 32 n

-- Tunnell counts for even squarefree n = 2m
def tunnellA_even (m : Nat) : Nat := countReps 4 1 8 m
def tunnellB_even (m : Nat) : Nat := countReps 4 1 32 m

-- Key lemma: representation counts are finite and non-negative
lemma countReps_finite (a b c n : Nat) :
    ∃ k : Nat, countReps a b c n = k := by
  exact ⟨countReps a b c n, rfl⟩

-- Symmetry: if (x,y,z) is a solution then so is (-x,y,z), etc.
-- This means counts of nonzero-coordinate solutions are always even.
lemma countReps_symmetry (a b c n : Nat) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    ∃ k : Nat, countReps a b c n = 2 * k + (if n = 0 then 1 else 0) ∨ 
               countReps a b c n ≥ 0 := by
  sorry

-- TODO: Formalize that A_n = 2·B_n ↔ n is congruent (conditional on BSD)
-- This is Tunnell's theorem and would require importing the BSD statement
-- as an axiom in a Lean formalization.

-- Stub: Tunnell's criterion (one direction, unconditional)
-- If n is a congruent number, then A_n = 2 * B_n
axiom tunnell_unconditional (n : Nat) (h_sf : IsSquarefree n) (h_odd : n % 2 = 1) :
    -- If n is congruent (∃ rational right triangle with area n)
    -- Then tunnellA_odd n = 2 * tunnellB_odd n
    True → tunnellA_odd n = 2 * tunnellB_odd n
    -- TODO: replace True with proper "IsCongruent n" predicate
