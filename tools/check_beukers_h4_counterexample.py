#!/usr/bin/env python3
"""Exact rational arithmetic certificate for the false positivity in 6.3(2).

The analytic enclosure is derived in docs/BEUKERS_POSITIVITY_COUNTEREXAMPLE.md.
This checker uses no floating point and is not a Lean kernel certificate.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
c = json.loads((ROOT / "provenance/beukers_cone_h4_certificate.json").read_text())
assert (c["h"], c["K"], c["truncation_N"]) == (4, 28, 240)
V = [[F(x) for x in row] for row in c["basis_Q"]]
assert len(V) == 4 and all(len(v) == 16 for v in V)
# RREF free coordinates certify independence, without a numerical rank test.
assert [[v[j] for j in range(12, 16)] for v in V] == [
    [F(i == j) for j in range(4)] for i in range(4)]

def expand(q):
    return [sum(q[j] * (-1)**(r-8-j) * comb(4, r-8-j)
                for j in range(16) if 0 <= r-8-j <= 4)
            for r in range(29)]

def constraints(p):
    return [sum(p[r] * (F(factorial(v), (r+m+1)**(v+1)) -
                        F(factorial(5-v), (r+m+1)**(6-v)))
                for r in range(29)) for m in range(4) for v in range(3)]

C = [expand(v) for v in V]
assert C == [[F(x) for x in row] for row in c["basis_P"]]
assert all(all(x == 0 for x in constraints(p)) for p in C)
t = F(6478719102356089, 10**15)
assert F(c["t"]) == t
q = [b-t*a for a, b in zip(V[0], V[1])]
p = expand(q)
assert p == [F(x) for x in c["P_coefficients"]]
assert q == [F(x) for x in c["Q_coefficients"]]
assert constraints(p) == [F(0)] * 12
assert sum(abs(x) for x in q) == F(c["Q_l1"]) > 0

H6 = [sum(F(1, j**6) for j in range(1, r+1)) for r in range(29)]
H7 = [sum(F(1, j**7) for j in range(1, r+1)) for r in range(29)]
slope = sum(x*x for x in p)
constant = sum(p[r]*p[s]*(-H7[r] if r == s else
                         (H6[r]-H6[s])/(6*(r-s)))
               for r in range(29) for s in range(29))
assert slope == F(c["slope"]) > 0
assert constant == F(c["constant"])

N = 240
eta = sum(F(1, 2**(k+1)) * sum(F((-1)**j * comb(k, j), (j+1)**7)
                                for j in range(k+1)) for k in range(N))
lo = F(64, 63)*eta
hi = F(64, 63)*(eta+F(1, 2**N))
assert eta == F(c["eta_euler_partial"])
assert lo == F(c["zeta_lower"]) and hi == F(c["zeta_upper"])
lower, upper = constant+slope*lo, constant+slope*hi
assert lower == F(c["quadratic_lower"])
assert upper == F(c["quadratic_upper"])
assert -F(12115, 10**52) < lower <= upper < -F(12114, 10**52)
# The normalized four-polynomial basis satisfies the printed l1 condition.
normalized_basis = [[x/sum(abs(y) for y in v) for x in v] for v in V]
assert all(sum(abs(x) for x in v) == 1 for v in normalized_basis)
print("EXACT_RATIONAL_CERTIFICATE_PASS: h=4, K=28, twelve constraints zero,")
print("four independent normalized basis polynomials, negative quadratic value.")
print("Analytic zeta enclosure: documented finite geometric-series argument.")
print("Verification scope: independent rational computation, not Lean kernel.")
