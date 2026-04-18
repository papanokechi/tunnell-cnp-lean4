# congruent-relay

Computational evidence for congruent numbers up to N = 500, produced by a
Scout → Architect → Prober → Synthesizer relay.

## Quick start

```bash
python -m venv .venv
source .venv/bin/activate   # Windows: .venv\Scripts\activate
pip install -r requirements.txt
pytest -q                   # verify environment
python -m src.runner --max-n 50   # baseline run
```

## Project layout

```
src/           Core library (counts, elliptic utils, PSLQ, runner)
tests/         Pytest suite
data/          Output CSVs (generated)
logs/          Run logs with provenance
docs/          Problem spec, bibliography, evidence summary
formal/        Lean 4 lemma stubs
```

## Conditional statements

Any result linking Tunnell counts to congruent-number status is
**conditional on the Birch and Swinnerton-Dyer conjecture**.
All outputs are labeled accordingly.

## Reproducibility

`Dockerfile` provided. A fresh clone + install + `python -m src.runner`
must reproduce `data/results.csv`.

## License

MIT
