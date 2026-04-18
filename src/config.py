# src/config.py — global parameters for congruent-relay
"""Central configuration.  Import from here so every module uses the same knobs."""

N = 500                           # upper bound for the scan
PRECISION_SCHEDULE = [100, 300, 1000]   # decimal digits for PSLQ ramps
RESULTS_CSV = "data/results.csv"
LOGS_DIR = "logs"

# bounds for brute-force Tunnell form counting (max |x|,|y|,|z| search)
# automatically derived from n at runtime, but we cap it here for safety
FORM_SEARCH_CAP = 10_000

# triangle witness search — max denominator for parametric search
TRIANGLE_DENOM_BOUND = 5000

# PSLQ
PSLQ_MAXCOEFF = 100_000
PSLQ_MAXSTEPS = 10_000
