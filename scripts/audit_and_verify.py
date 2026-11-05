#!/usr/bin/env python3
"""
audit_and_verify.py

Reproducible audit and variable-reduction calculator for Elliot Glazer's
explicit Diophantine definition of Z in Q (`elliotglazer/diophantine-z-q`).

Usage:
  1. Standalone exact accounting verification (no external files required):
       python3 scripts/audit_and_verify.py
  2. Full JSON DAG reachability & 3,181,317-digit program decoding audit
     (given a local clone of https://github.com/elliotglazer/diophantine-z-q):
       python3 scripts/audit_and_verify.py --diophantine-zq-dir /path/to/diophantine-z-q
"""

from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# 1. Exact Hierarchical Witness Accounting (Matches DiophantineZQ/ReductionAnalysis.lean)
# ---------------------------------------------------------------------------

SLOPE_WITNESSES = 1298
MEMBER_WITNESSES = 7
HEIGHT_CERT_WITNESSES = 3 * MEMBER_WITNESSES + 9 + 9 + 21 + 27 * SLOPE_WITNESSES  # 35,106
MULTIPLY_WITNESSES = 20 + 4 + 1 + 3 + HEIGHT_CERT_WITNESSES  # 35,134
RAW_ADD_WITNESSES = 6
NATURAL_GUARD_WITNESSES = 20 + 20 + 15 + 4 * MULTIPLY_WITNESSES + 2 * RAW_ADD_WITNESSES + 1  # 140,604

POWER_VALUE_WITNESSES = (
    3
    + 79 * 5
    + 79 * NATURAL_GUARD_WITNESSES
    + 3 * 6
    + 196 * (5 + RAW_ADD_WITNESSES)
    + 190 * (5 + MULTIPLY_WITNESSES)
)  # 17,786,698

POSITIVE_BASE_POWER_VALUE_WITNESSES = (
    3
    + 77 * 5
    + 77 * NATURAL_GUARD_WITNESSES
    + 3 * 6
    + 192 * (5 + RAW_ADD_WITNESSES)
    + 186 * (5 + MULTIPLY_WITNESSES)
)  # 17,364,880

NON_PRECISION_RAT_WITNESSES = (
    5 + 7 + 406 + 5 + 35282 + 40 + 5 * 140654 + 53
)  # 739,068


def precision_rat_witnesses(
    explicit_witnesses: int,
    num_constants: int,
    num_adds: int,
    num_muls: int,
    num_powers: int,
    per_power_witnesses: int = POWER_VALUE_WITNESSES,
) -> int:
    return (
        3
        + explicit_witnesses * 5
        + (5 + explicit_witnesses) * NATURAL_GUARD_WITNESSES
        + num_constants * 6
        + num_adds * (5 + RAW_ADD_WITNESSES)
        + num_muls * (5 + MULTIPLY_WITNESSES)
        + num_powers * (5 + per_power_witnesses)
    )


def verify_exact_counts() -> None:
    assert HEIGHT_CERT_WITNESSES == 35106
    assert MULTIPLY_WITNESSES == 35134
    assert NATURAL_GUARD_WITNESSES == 140604
    assert POWER_VALUE_WITNESSES == 17786698
    assert POSITIVE_BASE_POWER_VALUE_WITNESSES == 17364880
    assert NON_PRECISION_RAT_WITNESSES == 739068

    # Baseline (Glazer's diophantine-z-q)
    base_nat = 5 + 54051 + 15845 * 79
    base_prec_rat = precision_rat_witnesses(54051, 4, 125327, 98382, 15845, POWER_VALUE_WITNESSES)
    base_rat = NON_PRECISION_RAT_WITNESSES + base_prec_rat
    assert base_nat == 1305811
    assert base_prec_rat == 292889492836
    assert base_rat == 292890231904

    # Stage 1: Single-Fold Complement-Mask Zero-Tests + Functional Elimination
    s1_nat = 5 + 29731 + 8489 * 79
    s1_rat = NON_PRECISION_RAT_WITNESSES + precision_rat_witnesses(
        29731, 4, 70565, 54282, 8489, POWER_VALUE_WITNESSES
    )
    assert s1_nat == 700367
    assert s1_rat == 157081401474

    # Stage 2: Shared Binomial Numerators (F, D) + Combined Disjointness-in-D
    s2_powers = 2 + (2 + 2421) + (2 + 204)
    assert s2_powers == 2631
    s2_nat = 5 + 15971 + s2_powers * 79
    s2_rat = NON_PRECISION_RAT_WITNESSES + precision_rat_witnesses(
        15971, 4, 41855, 30130, s2_powers, POWER_VALUE_WITNESSES
    )
    assert s2_nat == 223825
    assert s2_rat == 50103122522

    # Stage 3: Stage 2 + Positive-Base Specialization of power_value (1 <= Q)
    s3_nat = 5 + 15971 + s2_powers * 77
    s3_rat = NON_PRECISION_RAT_WITNESSES + precision_rat_witnesses(
        15971, 4, 41855, 30130, s2_powers, POSITIVE_BASE_POWER_VALUE_WITNESSES
    )
    assert s3_nat == 218563
    assert s3_rat == 48993319364

    print("================================================================================")
    print(" Exact Kernel-Verified Witness Accounting for Z-in-Q (diophantine-z-q)")
    print("================================================================================")
    rows = [
        ("Baseline (Glazer diophantine-z-q)", 15845, base_nat, base_rat),
        ("Stage 1 (Single-Fold Zero-Test)", 8489, s1_nat, s1_rat),
        ("Stage 2 (Shared F,D + Disjoint-D)", 2631, s2_nat, s2_rat),
        ("Stage 3 (Stage 2 + Positive-Base)", 2631, s3_nat, s3_rat),
    ]
    print(f"{'Stage':<35} | {'power Calls':>11} | {'Total N Vars':>12} | {'Total Q Witnesses':>17} | {'Factor':>7}")
    print("-" * 92)
    for label, pcalls, nvars, qwits in rows:
        factor = base_rat / qwits
        print(f"{label:<35} | {pcalls:>11,d} | {nvars:>12,d} | {qwits:>17,d} | {factor:>6.2f}x")
    print("================================================================================")


def audit_json_artifacts(repo_dir: Path) -> None:
    sys.set_int_max_str_digits(10_000_000)
    pnp_path = repo_dir / "construction" / "precision-natural-polynomial.json"
    oid_path = repo_dir / "construction" / "ordinary-integer-definition.json"

    if not pnp_path.exists() or not oid_path.exists():
        print(f"[!] Could not find construction JSON files under {repo_dir}")
        return

    print(f"\n[*] Auditing {pnp_path} ...")
    with open(pnp_path) as f:
        pnp = json.load(f)
    prog = pnp["polynomial"]
    nodes = prog["nodes"]
    root = prog["root"]

    # Reachability from root
    visited = set()
    stack = [root]
    while stack:
        idx = stack.pop()
        if idx in visited:
            continue
        visited.add(idx)
        node = nodes[idx]
        op = node["op"]
        if op in ("add", "sub", "mul"):
            stack.extend(node["args"])

    used_vars = {nodes[i]["index"] for i in visited if nodes[i]["op"] == "var"}
    print(f"    Explicit N variables: {len(prog['variables']):,d} (active in root DAG: {len(used_vars):,d})")
    print(f"    power template calls: {len(prog['calls']):,d}")

    # Decode 3,181,317-digit program code at node 0
    e_val = int(nodes[0]["value"])
    n_plus_1 = e_val + 1
    b_shift = (n_plus_1 & -n_plus_1).bit_length() - 1
    b = 4 * b_shift
    d_val = ((n_plus_1 >> b_shift) - 1) >> 1
    raw_bytes = d_val.to_bytes((d_val.bit_length() + 7) // 8, "little")
    block_bytes = b // 8
    num_states = len(raw_bytes) // block_bytes
    print(f"    Decoded node 0 program constant e ({len(nodes[0]['value']):,d} decimal digits):")
    print(f"      b = {b} bits/instruction, states s = {num_states:,d}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Verify Z-in-Q witness reductions and audit artifacts.")
    parser.add_argument(
        "--diophantine-zq-dir",
        type=Path,
        default=None,
        help="Optional path to a local clone of elliotglazer/diophantine-z-q",
    )
    args = parser.parse_args()
    verify_exact_counts()
    if args.diophantine_zq_dir is not None:
        audit_json_artifacts(args.diophantine_zq_dir)
