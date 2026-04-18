# src/pslq_hunt.py — PSLQ-based search for closed forms of L-values
"""
For E_n : y^2 = x^3 - n^2 x, the L-function value L(E_n, 1) determines
the rank (under BSD).  When L(E_n, 1) != 0, we can hunt for a closed
form in terms of known constants (pi, Omega_n, etc.).

Workflow:
  1. Compute L(E_n, 1) to increasing precision.
  2. Build a PSLQ basis of candidate constants.
  3. Run PSLQ and record any integer relation found.
"""

from __future__ import annotations
import json, os, time
from typing import Optional, List, Dict, Any

from mpmath import mp, mpf, pi, sqrt, agm, ellipk, gamma, pslq, nstr, fabs


def compute_L_value_approx(n: int, dps: int = 50, num_terms: int = 50000) -> mpf:
    """
    Approximate L(E_n, 1) via the Dirichlet-series / functional-equation
    approach.  Uses the theta-series method:

        L(E_n, 1) = (2 / sqrt(N_cond)) * sum_{m=1}^{inf} a_m / m * exp(-2 pi m / sqrt(N_cond))

    where N_cond is the conductor and a_m are the Fourier coefficients.
    We compute a_m naively for small m.

    This is a pedagogical implementation.  For production, use PARI's
    elllseries() via cypari2.
    """
    mp.dps = dps + 20
    N_cond = 32 * n * n  # rough conductor for odd squarefree n

    # Compute a_p for primes p by counting points mod p
    # a_p = p - #{(x,y) in (Z/pZ)^2 : y^2 = x^3 - n^2 x}
    # For full L-series we need all a_m, but we approximate with a_p for primes.
    # Multiplicative extension for prime powers.

    sqrt_N = sqrt(mpf(N_cond))
    exp_factor = 2 * pi / sqrt_N
    total = mpf(0)

    # Simple: count E_n(F_p) for each prime p via brute force
    # Then use a_m via multiplicativity
    from sympy import isprime

    a_coeffs = {}
    for p_int in range(2, min(num_terms + 1, 2000)):
        if not isprime(p_int):
            continue
        p = p_int
        count = 0
        n_sq_mod = (n * n) % p
        for x in range(p):
            rhs = (x * x * x - n_sq_mod * x) % p
            for y in range(p):
                if (y * y) % p == rhs:
                    count += 1
        a_p = p - count
        a_coeffs[p] = a_p

    # Build a_m for m = 1..num_terms using multiplicativity (primes only approx)
    # For a rough estimate, use only prime terms
    result = mpf(0)
    for p, a_p in a_coeffs.items():
        from mpmath import exp as mpexp
        term = mpf(a_p) / mpf(p) * mpexp(-exp_factor * mpf(p))
        result += term

    result *= 2 / sqrt_N
    mp.dps = dps
    return +result  # round to requested dps


def compute_L_value_pari(n: int, dps: int = 50) -> Optional[mpf]:
    """Compute L(E_n, 1) via cypari2 if available."""
    try:
        import cypari2
        pari = cypari2.Pari()
        pari.default("realprecision", dps + 10)
        E = pari(f"ellinit([0,0,0,-{n*n},0])")
        L_val = pari(f"elllseries({E}, 1)")
        mp.dps = dps
        return mpf(str(L_val))
    except Exception:
        return None


def compute_period(n: int, dps: int = 50) -> mpf:
    """
    Real period Omega of E_n : y^2 = x^3 - n^2 x.
    Omega = 2 * integral_n^infty dx / sqrt(x^3 - n^2 x)
          = 2 * Gamma(1/4)^2 / (sqrt(2*pi) * n^{1/2} * 2)   (for j=1728 curves)

    More precisely, for y^2 = x^3 - n^2 x with n>0:
    Omega = Gamma(1/4)^2 / (2^{1/2} * pi^{1/2} * n^{1/2})
    """
    mp.dps = dps + 20
    g14 = gamma(mpf(1) / 4)
    omega = g14 ** 2 / (sqrt(2 * pi) * sqrt(mpf(n)))
    mp.dps = dps
    return +omega


def build_basis(n: int, dps: int = 100) -> List[mpf]:
    """
    Build a PSLQ basis for hunting L-value relations.
    Basis: [L(E_n,1), 1, Omega_n, Omega_n * pi, Omega_n / pi, pi]
    """
    mp.dps = dps + 30

    L_val = compute_L_value_pari(n, dps + 20)
    if L_val is None:
        L_val = compute_L_value_approx(n, dps + 20)

    omega = compute_period(n, dps + 20)

    mp.dps = dps
    basis = [
        +L_val,
        mpf(1),
        +omega,
        +(omega * pi),
        +(omega / pi),
        +pi,
    ]
    return basis


def run_pslq_hunt(n: int, dps: int = 100, maxcoeff: int = 100000) -> Dict[str, Any]:
    """
    Run PSLQ on L(E_n,1) against a basis of known constants.
    Returns a dict with results and metadata.
    """
    mp.dps = dps
    basis = build_basis(n, dps)

    t0 = time.time()
    rel = pslq(basis, maxcoeff=maxcoeff, maxsteps=10000)
    elapsed = time.time() - t0

    result = {
        "n": n,
        "dps": dps,
        "basis_labels": ["L(E_n,1)", "1", "Omega_n", "Omega_n*pi", "Omega_n/pi", "pi"],
        "basis_values": [nstr(v, 15) for v in basis],
        "relation": rel,
        "elapsed_s": round(elapsed, 2),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }

    if rel is not None and rel[0] != 0:
        result["status"] = "candidate_found"
    elif rel is not None and rel[0] == 0:
        result["status"] = "basis_dependency"
    else:
        result["status"] = "no_relation"

    return result


def hunt_range(n_start: int, n_end: int, dps: int = 100,
               outfile: str = "data/pslq_results.jsonl") -> List[Dict]:
    """Run PSLQ hunts for all squarefree n in [n_start, n_end]."""
    from src.counts import is_squarefree, is_congruent_tunnell
    results = []
    os.makedirs(os.path.dirname(outfile) or ".", exist_ok=True)

    for n in range(n_start, n_end + 1):
        if not is_squarefree(n):
            continue
        # Only hunt non-congruent candidates (L != 0) where PSLQ can find closed form
        tunnell_congruent = is_congruent_tunnell(n)
        if tunnell_congruent:
            continue  # L(E_n,1) should be 0; skip

        try:
            res = run_pslq_hunt(n, dps=dps)
            res["tunnell_congruent"] = tunnell_congruent
            results.append(res)
            with open(outfile, "a") as f:
                f.write(json.dumps(res) + "\n")
        except Exception as e:
            results.append({"n": n, "error": str(e)})

    return results
