/-
ElementaryPNT.Stage4c — Stage 4, the smoothing chain ("Selberg's inequality eats its tail") and the prime number theorem.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage3
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4b
import ElementaryPNT.Stage4cAux
import ElementaryPNT.Stage4cStep1
import ElementaryPNT.Stage4cStep2
import ElementaryPNT.Stage4cStep3
import ElementaryPNT.Stage4cStep4

open Filter Topology

namespace SelbergPNT

/-- (chapter step S4.1a). With an explicit
constant: there is `C₁ > 0` with

  `|S(y) log y + ∑_{n ≤ y} S(y/n) Λ(n)| ≤ C₁ y`  for all `y ≥ 2`.

Chapter proof: divide `selberg_first` (constant 102) by `x` and integrate from `2` to
`y`. Two evaluations then finish it.
* `∫₂^y (R(x)/x) log x dx = log y · S(y) − ∫₂^y S(x)/x dx` by parts, writing
  `(R(x)/x) log x dx = log x d(S(x))`; the remaining integral is `O(y)` because `|S(x)/x| ≤ 1`
  (`abs_S_le`). The integration by parts needs only the **right** derivative of `S`,
  as the `Stage4bAux.hasDerivWithinAt_S` supplies.
* `∫₂^y R(x/n) dx/x = S(y/n) − S(2/n)`, by the substitution `x ↦ x/n`, and `|S(2/n)| ≤ 1`;
  summing over `n ≤ y` costs `∑_{n ≤ y} Λ(n) = ψ(y) ≤ 2y` .
The `log y` in the statement is the one produced by the first evaluation; nothing here needs
`log y` to be bounded. -/
theorem selberg_S_form_const :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ y : ℝ, 2 ≤ y →
      |S y * Real.log y + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, S (y / n) * ArithmeticFunction.vonMangoldt n|
        ≤ C₁ * y := by
  obtain ⟨C₁, hC₁, h⟩ := Stage4cStep1.selberg_S_form
  exact ⟨C₁, hC₁, fun y hy => h y (by linarith)⟩

/-- (chapter step S4.1b). There is `C₂ > 0` with

  `|S(y)(log y)² + ∑_{m ≤ y} (Λ(m) log m − (Λ∗Λ)(m)) S(y/m)| ≤ C₂ y log y`  for `y ≥ 2`.

Chapter proof: multiply by `log y`; then substitute `y ↦ y/k` in R14-1, multiply by `Λ(k)`,
and sum over `k ≤ y`. The second family gives
`∑_k Λ(k) S(y/k) log(y/k) + ∑_{k} ∑_{n ≤ y/k} Λ(k)Λ(n) S(y/(kn))`, with error
`∑_{k ≤ y} C₁ (y/k) Λ(k) = C₁ y ∑_{k ≤ y} Λ(k)/k ≤ C₁ y (log y + 9)` by Mertens .
Subtracting, the `log(y/k)` splits as `log y − log k`, the `log y` parts cancel against the first
family, and the double sum collapses by the hyperbola reindexing of an earlier stage (`Stage1Aux`) to
`∑_{m ≤ y} (Λ∗Λ)(m) S(y/m)`.

**This is the step an earlier review corrected**: the coefficient is
`Λ(m) log m − (Λ∗Λ)(m)`, not `Λ₂(m) = Λ(m) log m + (Λ∗Λ)(m)`; the `Λ₂` form appears only after
the triangle inequality in R14-3. The explicit constant in is what licenses summing a
family whose size grows with `y`. -/
theorem S_log_sq_eq_const :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ y : ℝ, 2 ≤ y →
      |S y * (Real.log y) ^ 2 +
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
          (ArithmeticFunction.vonMangoldt m * Real.log m -
            ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
              ArithmeticFunction.vonMangoldt (m / d)) * S (y / m)|
        ≤ C₂ * y * Real.log y := by
  exact Stage4cStep2.S_log_sq_eq

/-- (chapter step S4.1c). There is `C₃ > 0` with

  `|S(y)|(log y)² ≤ 2 ∑_{m ≤ y} |S(y/m)| log m + C₃ y log y`  for `y ≥ 2`.

Chapter proof: from by the triangle inequality,
`|S(y)|(log y)² ≤ ∑_{m ≤ y} |Λ(m) log m − (Λ∗Λ)(m)| |S(y/m)| + C₂ y log y`, and
`|Λ(m) log m − (Λ∗Λ)(m)| ≤ Λ(m) log m + (Λ∗Λ)(m) = Λ₂(m)`, both terms being nonnegative. Then
`∑_{m ≤ y} Λ₂(m) |S(y/m)| ≤ 2 ∑_{m ≤ y} |S(y/m)| log m + C y log y` by stage 10's
`selberg_second'` (`∑_{m ≤ y}(Λ₂(m) − 2 log m) = O(y)`) together with `|S(y/m)| ≤ y/m ≤ y`
(`abs_S_le`) — the Abel-summation form of that step, if the crude one loses too much,
is `∑ (Λ₂(m) − 2 log m) |S(y/m)|` bounded by partial summation against the monotone `m ↦ y/m`. -/
theorem abs_S_log_sq_le_sum_const :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ y : ℝ, 2 ≤ y →
      |S y| * (Real.log y) ^ 2 ≤
        2 * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, |S (y / m)| * Real.log m) + C₃ * y * Real.log y := by
  exact Stage4cStep3.abs_S_log_sq_le_sum

/-- (chapter step S4.1d). There is `C₄ > 0` with

  `|S(y)|(log y)² ≤ 2 ∫₂^y |S(y/u)| log u du + C₄ y log y`  for `y ≥ 2`.

Chapter proof: `|S(y/m)| log m ≤ ∫_m^{m+1} |S(y/m)| log u du`, and
`∫_m^{m+1} |S(y/m)| log u du ≤ ∫_m^{m+1} |S(y/u)| log u du + c(y/m − y/(m+1)) ∫_m^{m+1} log u du`
by the Lipschitz property of `S` (`S_lipschitz`, with `c = 1`). Since
`∫_m^{m+1} log u du ≤ log(y+1)` for `m ≤ y`, and `∑_{2 ≤ m ≤ y} (1/m − 1/(m+1)) ≤ 1/2`
telescopes, the total error is at most `(1/2) y log(y+1)`, which is `O(y log y)`. -/
theorem abs_S_log_sq_le_integral_const :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ y : ℝ, 2 ≤ y →
      |S y| * (Real.log y) ^ 2 ≤
        2 * (∫ u in (2 : ℝ)..y, |S (y / u)| * Real.log u) + C₄ * y * Real.log y := by
  exact Stage4cStep4.abs_S_log_sq_le_integral

/-- (chapter step S4.1). The blueprint's `W_le_average`:

  `|W(x)| ≤ (2/x²) ∫₀^x |W(v)|(x − v) dv + K/x`  eventually.

Chapter proof: put `y = eˣ` in and substitute `u = e^{x−v}`, so `du = −e^{x−v} dv`,
`log u = x − v`, and `y/u = e^v`. Then
`∫₂^y |S(y/u)| log u du = ∫_0^{x − log 2} |S(e^v)| (x − v) e^{x−v} dv
 = eˣ ∫_0^{x − log 2} |W(v)| (x − v) dv`, since `|S(e^v)| = e^v |W(v)|`. Dividing by
`eˣ x²` gives the claim, the range `[x − log 2, x]` contributing at most `|W| ≤ 1`
(`abs_W_le_one`) times `log 2 · x`, absorbed into `K/x`. -/
theorem W_le_average :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      |W x| ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, |W v| * (x - v)) + K / x := by
  exact Stage4cStep4.W_le_average

/-! ## The prime number theorem -/

/-- R14-6. **The prime number theorem.** `π(n)/(n/log n) → 1`.

Proof: `primeCounting_asymptotic_of_smoothing (smoothing_tr_of_smoothing_abs W_le_average)`,
both from stage 13. -/
theorem primeCounting_asymptotic :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
  exact primeCounting_asymptotic_of_smoothing (smoothing_tr_of_smoothing_abs W_le_average)

/-- R14-7. `ψ(x) ∼ x`, the other classical form. Proof: `psi_asymptotic_of_S`  applied
to `S_div_tendsto_zero_of_smoothing` . -/
theorem psi_asymptotic : Tendsto (fun x : ℝ => psi x / x) atTop (𝓝 1) := by
  exact psi_asymptotic_of_S
    (S_div_tendsto_zero_of_smoothing (smoothing_tr_of_smoothing_abs W_le_average))

open Classical in
end SelbergPNT
