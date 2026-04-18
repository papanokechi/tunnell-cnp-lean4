# src/runner.py — orchestrate full congruent-number scan
"""
Main entry point.  Run as:  python -m src.runner [--max-n N] [--mode MODE]

Modes:
  counts   — Tunnell counting only (fast)
  full     — counts + invariants + triangle witness search
  pslq     — counts + PSLQ hunt on non-congruent L-values
"""

from __future__ import annotations
import argparse
import csv
import json
import os
import sys
import time
from typing import List, Dict, Any

from src.config import N, RESULTS_CSV, LOGS_DIR
from src.counts import is_squarefree, count_tunnell_forms, is_congruent_tunnell
from src.elliptic_utils import compute_invariants


def run_counts(max_n: int) -> List[Dict[str, Any]]:
    """Run Tunnell counts for all squarefree n <= max_n."""
    rows = []
    for n in range(1, max_n + 1):
        if not is_squarefree(n):
            continue
        A, B = count_tunnell_forms(n)
        congruent = (A == 2 * B)
        rows.append({
            "n": n,
            "squarefree": True,
            "A_n": A,
            "B_n": B,
            "tunnell_congruent": congruent,
            "note": "conditional on BSD" if congruent else "",
        })
    return rows


def run_full(max_n: int, triangle_bound: int = 300) -> List[Dict[str, Any]]:
    """Run counts + invariants + optional triangle witness search."""
    from src.scan_triangles import find_witness
    rows = []
    for n in range(1, max_n + 1):
        if not is_squarefree(n):
            continue
        A, B = count_tunnell_forms(n)
        congruent = (A == 2 * B)
        inv = compute_invariants(n)

        witness = None
        if congruent:
            witness = find_witness(n, denom_bound=triangle_bound,
                                   height_bound=triangle_bound)

        row = {
            "n": n,
            "squarefree": True,
            "A_n": A,
            "B_n": B,
            "tunnell_congruent": congruent,
            "discriminant": inv["discriminant"],
            "conductor_est": inv["conductor_estimate"],
            "torsion": inv["torsion"],
            "witness_found": witness is not None,
            "witness": json.dumps({k: str(v) for k, v in witness.items()}) if witness else "",
            "note": "conditional on BSD",
        }
        rows.append(row)
    return rows


def write_csv(rows: List[Dict], path: str) -> None:
    """Write rows to CSV."""
    if not rows:
        return
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)


def write_log(rows: List[Dict], max_n: int, elapsed: float) -> None:
    """Write a provenance log."""
    os.makedirs(LOGS_DIR, exist_ok=True)
    log = {
        "max_n": max_n,
        "num_squarefree": len(rows),
        "num_congruent": sum(1 for r in rows if r.get("tunnell_congruent")),
        "elapsed_s": round(elapsed, 2),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "python": sys.version,
    }
    path = os.path.join(LOGS_DIR, f"run_{max_n}_{int(time.time())}.json")
    with open(path, "w") as f:
        json.dump(log, f, indent=2)
    return log


def main():
    parser = argparse.ArgumentParser(description="congruent-relay runner")
    parser.add_argument("--max-n", type=int, default=N, help=f"upper bound (default {N})")
    parser.add_argument("--mode", choices=["counts", "full", "pslq"], default="counts")
    parser.add_argument("--output", type=str, default=RESULTS_CSV)
    args = parser.parse_args()

    print(f"congruent-relay: mode={args.mode}, max_n={args.max_n}")
    t0 = time.time()

    if args.mode == "counts":
        rows = run_counts(args.max_n)
    elif args.mode == "full":
        rows = run_full(args.max_n)
    elif args.mode == "pslq":
        from src.pslq_hunt import hunt_range
        # Run counts first
        rows = run_counts(args.max_n)
        # Then PSLQ on non-congruent
        print("Starting PSLQ hunts on non-congruent numbers...")
        hunt_range(1, args.max_n, dps=100)
    else:
        rows = run_counts(args.max_n)

    elapsed = time.time() - t0
    write_csv(rows, args.output)
    log = write_log(rows, args.max_n, elapsed)

    n_cong = sum(1 for r in rows if r.get("tunnell_congruent"))
    print(f"Done: {len(rows)} squarefree tested, {n_cong} congruent (Tunnell)")
    print(f"Elapsed: {elapsed:.1f}s  |  Output: {args.output}")
    print(f"Log: {json.dumps(log, indent=2)}")


if __name__ == "__main__":
    main()
