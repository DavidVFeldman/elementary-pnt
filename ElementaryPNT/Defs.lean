/-
ElementaryPNT.Defs — the definitions: `psi`, `R`, `S`, `W`, `Λ₂`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib

namespace SelbergPNT

/-- `ψ(x) = ∑_{n ≤ x} Λ(n)`, as a function of a real variable. -/
noncomputable def psi (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- `R(x) = ψ(x) − x` (chapter, §"Exploiting Selberg's Inequality").

The chapter's convention `R(x) = 0` for `x < 2` is dropped here: with it,
`R x + x` is not monotone (it jumps down at `2`), which would make the
averages-to-values lemma of `Stage1.lean` vacuous. Without it, `R x + x = ψ x` is monotone, and
nothing downstream changes, since `S` integrates from `2` and `R` is bounded on `[0,2]`. -/
noncomputable def R (x : ℝ) : ℝ := psi x - x

/-- `S(x) = ∫₂^x R(u)/u du`. -/
noncomputable def S (x : ℝ) : ℝ := ∫ u in (2 : ℝ)..x, R u / u

/-- `W(u) = S(e^u)/e^u` (the chapter's exponential speedup). -/
noncomputable def W (u : ℝ) : ℝ := S (Real.exp u) / Real.exp u

/-- `Λ₂(n) = Λ(n) log n + ∑_{jk = n} Λ(j) Λ(k)`. -/
noncomputable def Lambda2 (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n +
    ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)

end SelbergPNT
