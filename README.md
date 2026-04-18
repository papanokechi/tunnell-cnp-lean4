# congruent-relay

**A Layered, Axiom-Isolated Formalization of the Congruent Number Problem
up to Tunnell's Criterion in Lean 4**

## Abstract

This project develops a fully self-contained Lean 4 formalization of the
combinatorial and structural components underlying Tunnell's criterion for
the congruent number problem, paired with a Python computational pipeline
producing evidence up to N = 500.

The formalization is organized into six layers, each mathematically natural
and axiom-free, culminating in a clean interface where the only remaining
assumptions are the Birch–Swinnerton-Dyer conjecture for the relevant
elliptic curves and Tunnell's conditional theorem.

### Formal contributions (`formal/CongruentStubs.lean` — 954 lines, zero sorry)

1. **Bound independence for ternary quadratic forms.**
   The bounded solution set `solSet t B` stabilizes for all B ≥ |t|, and
   `repCount t B` is constant beyond this canonical bound. Includes
   coordinate bounds, monotonicity, and bounded ↔ unbounded equivalence.

2. **Full sign symmetry.**
   All eight sign flips preserve solutions. The origin is the unique fixed
   point; all nonzero solutions occur in ±-pairs.

3. **Unbounded–bounded equivalence.**
   `solSet∞` (the mathematical solution set) is finite for positive-definite
   forms, with `↑(solSet t t.natAbs) = solSet∞ t` at the canonical bound.

4. **Orbit pairing and parity.**
   A generic `Finset` fixed-point-free involution lemma
   (`card_even_of_involution`) proved from first principles by strong
   induction. Instantiating with negation yields even cardinality of
   nonzero solutions and `repCount_even_of_pos`.

5. **Theta-series bridge.**
   `thetaCoeff` := `repCount` (combinatorial alias), proved equal to the
   cardinality of `solSet∞`. Provides the exact quantities in Tunnell's
   theorem.

6. **Tunnell's criterion under BSD.**
   `IsCongruentNumber`, `OnCurveEn`, opaque rank functions
   (`AlgebraicRank`, `AnalyticRank`), `BSD_for` (meaningful Prop),
   Tunnell conditional axiom. Both the unconditional forward
   direction and the reverse direction under BSD are corollaries.

**Final tally:** zero sorry, one explicit axiom (`tunnell_conditional_on_BSD`,
isolated in §6), two opaque rank functions (`AlgebraicRank`, `AnalyticRank`).
All earlier layers are fully constructive and self-contained.

### Computational contributions (`src/` — 98 tests, 1 skipped)

- **Tunnell counting** (`counts.py`): squarefree test, ternary quadratic
  form enumeration, Tunnell odd/even branching. Validated against
  OEIS A003273.
- **Elliptic utilities** (`elliptic_utils.py`): E_n curve construction,
  discriminant, j-invariant (always 1728), point ↔ triangle conversion.
- **Triangle witnesses** (`scan_triangles.py`): rational right triangle
  search via direct enumeration and curve-point lifting.
- **PSLQ hunts** (`pslq_hunt.py`): closed-form search for L(E_n, 1)
  using multi-constant bases.
- **Runner** (`runner.py`): orchestrator producing `data/results.csv`
  with modes `counts`, `full`, `pslq`.

## Quick start

```bash
python -m venv .venv
source .venv/bin/activate   # Windows: .venv\Scripts\activate
pip install -r requirements.txt
pytest -q                   # 98 pass, 1 skip
python -m src.runner --max-n 50   # baseline run
python -m src.runner --max-n 500  # full scan (185/306 congruent)
```

## Project layout

```
formal/            Lean 4 formalization (954 lines, 0 sorry, 1 axiom, 2 opaque)
  CongruentStubs.lean   §§1–6: definitions → Tunnell axiom
src/               Python computational pipeline
  counts.py            Tunnell counting
  elliptic_utils.py    E_n : y² = x³ − n²x
  pslq_hunt.py         PSLQ closed-form hunts on L-values
  scan_triangles.py    Rational triangle witness search
  runner.py            Orchestrator (--mode counts/full/pslq)
tests/             Pytest suite (98 pass)
data/              Output CSVs (generated)
docs/              Problem spec, bibliography, evidence summary
logs/              Run logs with provenance
```

## File tour: `formal/CongruentStubs.lean`

| Section | Lines | Key items |
|---------|-------|-----------|
| §1 Foundations | ~66–107 | `IsSquarefree`, `solSet`, `repCount` |
| §2 Basic properties | ~107–182 | `repCount_neg`, `repCount_nonneg`, `solSet_neg_x/y/z` |
| §3a Bound independence | ~182–287 | `solSet_mono`, `solSet_stable`, `repCount_stable` |
| §3b Sign symmetry | ~287–341 | `solSet_sign_symmetry`, `solSet_origin` |
| §3c Unbounded bridge | ~341–414 | `solSet∞`, `solSet∞_finite`, `solSet_eq_solSet∞` |
| §4 Orbit pairing | ~414–690 | `card_even_of_involution`, `repCount_even_of_pos` |
| §5 Theta series | ~754–849 | `thetaCoeff`, `thetaCoeff_eq_solSet∞_card` |
| §6 Tunnell axiom | ~849–end | `IsCongruentNumber`, `BSD_for`, `tunnell_conditional_on_BSD` |

## Conditional statements

Results linking Tunnell counts to congruent-number status are
**conditional on the Birch and Swinnerton-Dyer conjecture**.
This dependency is explicitly axiomatized in the Lean formalization
(`BSD_for`, `tunnell_conditional_on_BSD`) and labeled
in all computational outputs.

## Reproducibility

`Dockerfile` provided. A fresh clone → install → `python -m src.runner`
reproduces `data/results.csv`. The Lean formalization depends on
Mathlib4 for `Finset`, `Set`, `Int`, `Rat`, and standard algebraic
infrastructure. No additional libraries are required.

## Git history

```
a3820a9  bootstrap: Tunnell counting, elliptic utils, triangle search, PSLQ hunt
633b269  formal: replace stubs with sorry-free structural lemma package
31f5abd  formal: implement repCount via Finset enumeration + symmetry lemmas
fb656ad  formal: bound independence, full sign symmetry, unbounded bridge
fa3c8ea  formal: orbit pairing, theta series, Tunnell axiom (BSD)
1c4581c  formal: close all sorry's — Finset involution lemma + file tour
023c730  README: submission-ready project statement
95a5202  Address reviewer feedback: meaningful BSD, fix forward refs, clarify deps
```

## License

MIT
