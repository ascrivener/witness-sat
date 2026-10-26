#!/usr/bin/env python3
"""Fit the LRAT check's gas model to measurements.

    fit_gas.py GAS.tsv...

GAS.tsv is what scripts/gas.sh writes: a line a batch, with the counts the model in
tools/sat-report/src/plan.rs uses (hints, visits, witness bytes, hashes, trusted bytes) and the gas
witness-sim measured. Prints the nonnegative least-squares coefficients, and how far the fitted
model is from each measurement, as the worst under- and overestimate.
"""

import csv
import sys

import numpy as np

COLUMNS = ["hints", "visits", "witness_bytes", "hashes", "trusted_bytes"]

rows = []
for path in sys.argv[1:]:
    with open(path) as f:
        rows += [r for r in csv.DictReader(f, delimiter="\t") if int(r["steps"]) > 0]
X = np.array([[1.0] + [float(r[c]) for c in COLUMNS] for r in rows])
y = np.array([float(r["gas"]) for r in rows])
# Least squares, nonnegative: refit without any term that came out negative, until none does.
keep = list(range(X.shape[1]))
while True:
    sub = np.linalg.lstsq(X[:, keep], y, rcond=None)[0]
    if (sub >= 0).all():
        break
    keep = [k for k, c in zip(keep, sub) if c >= 0]
coef = np.zeros(X.shape[1])
coef[keep] = sub
fit = X @ coef
ratio = y / fit
print(f"{len(rows)} batches")
print("base", f"{coef[0]:.0f}")
for c, v in zip(COLUMNS, coef[1:]):
    print(c, f"{v:.1f}")
print(f"measured / fitted: {ratio.min():.3f} to {ratio.max():.3f}")
worst = max(range(len(rows)), key=lambda i: ratio[i])
r = rows[worst]
print(f"most underestimated: {r['input']} budget {r['budget']} batch {r['batch']}: {y[worst]:.3e} measured, {fit[worst]:.3e} fitted")
