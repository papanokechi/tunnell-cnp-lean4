# Problem specification: Congruent numbers up to N = 500

## Definition

A positive integer **n** is a *congruent number* if there exists a right triangle
with three **rational** side lengths whose area equals n.

Equivalently, n is congruent iff the elliptic curve
$$E_n : y^2 = x^3 - n^2 x$$
has a rational point of infinite order (i.e., algebraic rank ≥ 1).

## Conventions

- We consider only **squarefree** positive integers. A non-squarefree m
  is congruent iff its squarefree part is congruent.
- Sign convention: n > 0, sides a, b, c > 0 with a² + b² = c², area = ab/2 = n.
- Target range: **n = 1, 2, …, 500** (squarefree only → ~304 values).

## Tunnell's theorem (1983)

For **odd** squarefree n, define:
- A_n = #{(x,y,z) ∈ ℤ³ : 2x² + y² + 8z² = n}
- B_n = #{(x,y,z) ∈ ℤ³ : 2x² + y² + 32z² = n}

For **even** squarefree n (n = 2m):
- A_n = #{(x,y,z) ∈ ℤ³ : 4x² + y² + 8z² = m}
- B_n = #{(x,y,z) ∈ ℤ³ : 4x² + y² + 32z² = m}

**Theorem (Tunnell, 1983):**
- If n is congruent, then A_n = 2·B_n. *(unconditional)*
- If A_n = 2·B_n, then n is congruent. *(conditional on the Birch and Swinnerton-Dyer conjecture)*

## Known small examples

| n  | Congruent? | Triangle (a, b, c)          |
|----|------------|-----------------------------|
| 5  | Yes        | 20/3, 3/2, 41/6            |
| 6  | Yes        | 3, 4, 5                    |
| 7  | Yes        | 24/5, 35/12, 337/60        |
| 13 | Yes        | 780/323, 323/30, ...       |
| 1  | No         | —                           |
| 2  | No         | —                           |
| 3  | No         | —                           |

## Deliverable targets

1. Tunnell counts (A_n, B_n) for all squarefree n ≤ 500.
2. Cross-validation against OEIS A003273.
3. Explicit triangle witnesses for congruent n where computationally feasible.
4. PSLQ closed-form hunts on L(E_n, 1) for non-congruent n.
5. Minimal formal Lean stubs for counting lemmas.
