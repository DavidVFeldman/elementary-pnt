# An elementary proof of the prime number theorem, in Lean 4

A complete, machine-checked formalization of the elementary (Erdős–Selberg) proof of the prime
number theorem, following D. V. Feldman, *1896/1949 — The Elementary Proof of the Prime Number
Theorem*, a chapter of a book in preparation.

The main theorem, in `ElementaryPNT/Stage4c.lean`:

```lean
theorem SelbergPNT.primeCounting_asymptotic :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1)
```

and, in the same file, `ψ(x) ∼ x`.

The development uses no complex analysis: no zeta function, no contour integral, no Tauberian
theorem. It is about 5,500 lines and 214 theorems over Mathlib.

## What "machine-checked" means here

`Audit.lean` prints the axiom dependencies of the main theorem and of every named result of the
development. Each depends on at most `propext`, `Classical.choice` and `Quot.sound`; none depends
on `sorryAx`. No file contains `sorry`, `admit`, `axiom` or `native_decide`, and CI fails on any
of them. The kernel checks every numerical claim: the constants in `Stage4aCheb.lean` are
certified by rational inequalities against `2.7182818283 < e` and by `decide` on primorials, so no
floating-point arithmetic enters at any point.

## Layout, and the correspondence with the chapter

| File | Chapter sections | Content |
|---|---|---|
| `Defs.lean` | — | `ψ`, `R = ψ − id`, `S(x) = ∫₂ˣ R(u)/u du`, `W(u) = S(eᵘ)/eᵘ`, `Λ₂` |
| `Chebyshev.lean` | — | `ψ` agrees with Mathlib's; `log m! = ∑_{d ≤ m} Λ(d)⌊m/d⌋` |
| `Stage1.lean` | "How slow growth for averages…", "Some useful inequalities concerning factorials", "Chebychev's weak form", "Mertens' weak form", "A matrix approach to the Tatuzawa–Iseki identity" | averages to values; the factorial inequality; `ψ = O(x)`; Mertens with an explicit constant; the Tatuzawa–Iseki identity |
| `Stage1b.lean` | "A general tool for proving that certain functions have limit zero" and following | the three-condition criterion: a nonnegative Lipschitz function whose essential bound is at most its average bound, with a uniform bound on the integral over each interval where it does not vanish, tends to zero |
| `Stage3.lean` | "Selberg's inequality" | Selberg's inequality, in the `R`-form and the `Λ₂`-form |
| `Stage4a.lean` | "Bounding limsup \|S(y)\|/y", "A Lipschitz condition for \|W(x)\|" | `\|R(u)\| ≤ u`, `\|S(y)\| ≤ y − 2`, `\|W\| ≤ 1`; `S` is 1-Lipschitz; `\|W\|` is Lipschitz on `[0,∞)` |
| `Stage4aCheb.lean` | "Chebychev's weak form" | `ψ(x) ≤ 2x`, from scratch |
| `Stage4b.lean` | "A universal bound for ∫₂ˣ S(y)/y² dy", "Essential bounds for averages give essential bounds for values" | the two-way slicing; the universal gap bound; `α ≤ κ`; the endgame given the smoothing estimate |
| `Stage4c.lean` | "Selberg's Inequality eats its tail", "Replacing a sum by an integral", "Exponential speedup" | the smoothing chain, and the prime number theorem |
| `Stage5.lean` | "A smoothing transformation", "The equivalence of two forms of the Prime Number Theorem" | `S(x)/x → 0 ⟹ ψ(x) ∼ x ⟹ π(x) ∼ x/log x` |

`*Aux.lean`, `*Step*.lean`, `Stage1bWalk.lean`, `Stage4bGap.lean` and `Stage4bMertens.lean` hold
supporting lemmas for the file they are named after.

## Two by-products for Mathlib

`contrib/` holds two self-contained files, each stated for Mathlib's own `Chebyshev.psi`,
importing only Mathlib and depending on nothing else here:

* `Chebyshev_lower.lean` — Chebyshev's lower bound, `x log 2 − log x − log 4 ≤ ψ(x)`, hence
  `x = O(ψ(x))`. The file `Mathlib/NumberTheory/Chebyshev.lean` lists this as a TODO.
* `Chebyshev_psi_le_two.lean` — `ψ(x) ≤ 2x`, sharpening Mathlib's `Chebyshev.psi_le_const_mul_self`
  from `log 4 + 4 ≈ 5.386` to `2`.

Together they give a two-sided Chebyshev estimate with clean constants. They are prepared, not
submitted; `contrib/README.md` records what each proves, what it uses, and where it would sit.

## Building

```
lake exe cache get
lake build
```

Lean and Mathlib versions are pinned by `lean-toolchain` and `lake-manifest.json`.

## Structure of the proof

Selberg's inequality is the arithmetic input:
`∑_{n ≤ x} Λ₂(n) = 2x log x + O(x)`, where `Λ₂(n) = Λ(n) log n + ∑_{jk=n} Λ(j)Λ(k)`. It is derived
from the Tatuzawa–Iseki identity, itself an operator computation `M⁻¹LM − L = T` on the transform
`(MF)(x) = ∑_{k ≤ x} F(x/k)`.

The analytic half contains no primes at all. Writing `R = ψ − id`, `S` for its logarithmic
integral and `W(u) = S(eᵘ)/eᵘ`, Selberg's inequality is smoothed until it "eats its tail" and
becomes `|W(x)| ≤ (2/x²)∫₀ˣ |W(v)|(x−v) dv + K/x`. That estimate, the Lipschitz property of `|W|`
and a universal bound on the integral of `|W|` over each interval where it does not vanish feed a
general criterion — a nonnegative function whose limsup is at most the limsup of its running
averages, under those two side conditions, tends to zero — and give `W → 0`. Undoing the smoothing
gives `ψ(x) ∼ x`, and partial summation gives `π(x) ∼ x/log x`.

## Provenance

The mathematics is the chapter's. The Lean development was produced with Aristotle (Harmonic)
under the author's direction, statement by statement, with a separate commissioning and review
step for each: every statement was fixed and reviewed before its proof was attempted, and every
delivery was checked for statement fidelity and re-audited. Several statements were found false in
review and are recorded as such in the file comments where the corrected version departs from the
first attempt.

## Before publishing

Four things need the author's decision, and are deliberately left undone here.

1. **A licence.** Apache 2.0 matches Mathlib and is the path of least resistance if the `contrib/`
   files are ever offered upstream.
2. **The `Authors:` field** in the two `contrib/` copyright headers, which Mathlib requires, and
   attribution for the Lean development generally.
3. **The chapter.** This repository cites it but does not include it. If it is not yet public,
   the citation should say where it will appear.
4. **The commit authorship.** The initial commit is authored `David V. Feldman <dvfinnh@gmail.com>`,
   taken from the companion report. To change it:
   `git commit --amend --author="Name <email>"`, or reset the whole history with
   `git -c user.name=… -c user.email=… commit --amend --reset-author --no-edit`.
