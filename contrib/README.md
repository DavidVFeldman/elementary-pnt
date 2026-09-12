# Prepared patches for Mathlib

Two self-contained files, each stated for Mathlib's own `Chebyshev.psi`, importing only Mathlib,
and depending on nothing else in this repository. Neither has been submitted.

## `Chebyshev_lower.lean`

Chebyshev's lower bound: `x log 2 − log x − log 4 ≤ ψ x` for `x ≥ 1`, hence `c·x ≤ ψ x` eventually
for every `c < log 2`, hence `x = O(ψ x)`.

`Mathlib/NumberTheory/Chebyshev.lean` lists "Prove Chebyshev's lower bound" as a TODO. That file
has the upper bounds `Chebyshev.theta_le_log4_mul_x` and `Chebyshev.psi_le_const_mul_self` but no
lower bound.

Proof: `log C(2n,n) ≤ ψ(2n)` from the identity `log m! = ∑_{d ≤ m} Λ(d)⌊m/d⌋`, together with
`4ⁿ/(2n+1) ≤ C(2n,n)`.

## `Chebyshev_psi_le_two.lean`

`ψ x ≤ 2x` for `x ≥ 0`, sharpening `Chebyshev.psi_le_const_mul_self`, whose constant is
`log 4 + 4 ≈ 5.386`.

Proof: for `x ≥ 400`, Mathlib's sharper `Chebyshev.psi_le` with a tangent-line bound on `log`; for
`2 ≤ x < 400`, four explicit bands from `ψ(x) = θ(x) + ∑_{n ≥ 2} θ(x^{1/n})`. Every numerical
logarithm is certified by a rational inequality against `2.7182818283 < e`, and every primorial by
`decide`, so no floating-point arithmetic enters.

## Before submitting

The copyright headers have an empty `Authors:` field, which Mathlib requires. Attribution for the
Lean proofs is the author's to decide; see the provenance note in the top-level README.
