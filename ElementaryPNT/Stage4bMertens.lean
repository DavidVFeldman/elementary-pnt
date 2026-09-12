/-
ElementaryPNT.Stage4bMertens — auxiliary development for `ElementaryPNT.Stage4b`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4bAux

open Filter Topology MeasureTheory

namespace SelbergPNT
namespace Stage4bMertens

/-! ## The steps of `ψ` -/

/-- On `[0, x]`, `ψ(t)` is the sum over `n ≤ ⌊x⌋₊` of the jumps that have already happened. -/
theorem psi_eq_sum_indicator {x t : ℝ} (ht0 : 0 ≤ t) (htx : t ≤ x) :
    psi t = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
  rw [psi, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, le_trans h2 (Nat.floor_le_floor htx)⟩, (Nat.le_floor_iff ht0).1 h2⟩
  · rintro ⟨⟨h1, -⟩, h3⟩
    exact ⟨h1, (Nat.le_floor_iff ht0).2 h3⟩

theorem measurable_step (n : ℕ) :
    Measurable (fun t : ℝ =>
      (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2) :=
  (Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const).div (measurable_id.pow_const 2)

theorem intervalIntegrable_step (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := (ArithmeticFunction.vonMangoldt n : ℝ) / a ^ 2)
    measure_Ioc_lt_top.ne (measurable_step n).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  filter_upwards with t ht
  have ht0 : 0 < t := lt_trans ha ht.1
  have hL : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)]
  have h1 : |(if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0)|
      ≤ ArithmeticFunction.vonMangoldt n := by
    split <;> simp [abs_of_nonneg hL, hL]
  have h2 : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1.le]
  calc |(if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0)| / t ^ 2
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / t ^ 2 := by gcongr
    _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / a ^ 2 := by gcongr

theorem integral_one_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (1 : ℝ) / t ^ 2) = 1 / a - 1 / b := by
  have h : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(1 / u)) (1 / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hab] at ht
      exact ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h2 := (hasDerivAt_inv ht0).neg
    convert h2 using 1
    · funext u; simp [one_div]
    · field_simp
  have hint : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (by fun_prop)
      fun t ht => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha ht.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h hint]
  field_simp
  ring

/-- The `n`-th jump contributes `Λ(n)(1/n − 1/x)` to `∫₂^x ψ(t)/t² dt`. -/
theorem integral_step (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 2 ≤ x) (hnx : (n : ℝ) ≤ x) :
    (∫ t in (2 : ℝ)..x,
        (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2)
      = ArithmeticFunction.vonMangoldt n / n - ArithmeticFunction.vonMangoldt n / x := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · have hL : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by rw [← h1]; simp
    simp [hL]
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_step n (a := (2 : ℝ)) (b := (n : ℝ)) (by norm_num) hn2)
      (intervalIntegrable_step n (a := (n : ℝ)) (b := x) (by linarith) hnx)
    have hlow : (∫ t in (2 : ℝ)..(n : ℝ),
        (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2) = 0 := by
      have hae : ∀ᵐ t : ℝ, t ≠ (n : ℝ) := by rw [ae_iff]; simp
      rw [show (0 : ℝ) = ∫ _t in (2 : ℝ)..(n : ℝ), (0 : ℝ) by simp]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with t ht hmem
      rw [Set.uIoc_of_le hn2] at hmem
      have hlt : t < (n : ℝ) := lt_of_le_of_ne hmem.2 ht
      simp [not_le.2 hlt]
    have hhigh : (∫ t in (n : ℝ)..x,
          (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2)
        = ArithmeticFunction.vonMangoldt n / n - ArithmeticFunction.vonMangoldt n / x := by
      have hcongr : (∫ t in (n : ℝ)..x,
            (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2)
          = ∫ t in (n : ℝ)..x, (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / t ^ 2) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hnx] at ht
        simp [ht.1]
        ring
      rw [hcongr, intervalIntegral.integral_const_mul, integral_one_div_sq (by linarith) hnx]
      field_simp
    rw [← hadd, hlow, hhigh, zero_add]

/-! ## The partial-summation identity and its consequence -/

/-- The partial-summation identity: `∫₂^x ψ(t)/t² dt = ∑_{n ≤ x} Λ(n)/n − ψ(x)/x`.

Proof: expand `ψ(t)` by `psi_eq_sum_indicator`, exchange the finite sum with the integral, and
evaluate each term by `integral_step`. -/
theorem integral_psi_div_sq_eq {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, psi t / t ^ 2) =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n) - psi x / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hstep : ∀ t ∈ Set.uIcc (2 : ℝ) x, psi t / t ^ 2
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    rw [psi_eq_sum_indicator (by linarith [ht.1]) ht.2, Finset.sum_div]
  rw [intervalIntegral.integral_congr hstep,
    intervalIntegral.integral_finset_sum
      (fun n _ => intervalIntegrable_step n (by norm_num) hx)]
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (∫ t in (2 : ℝ)..x,
          (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) / t ^ 2)
        = ArithmeticFunction.vonMangoldt n / n - ArithmeticFunction.vonMangoldt n / x := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnx : (n : ℝ) ≤ x :=
      le_trans (Nat.cast_le.2 hn.2) (Nat.floor_le (by linarith))
    exact integral_step n hn.1 hx hnx
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  congr 1
  rw [psi, ← Finset.sum_div]

/-- `∫₂^x R(t)/t² dt` is bounded independently of `x`: the `log x` of Mertens cancels the
`log x` of `∫₂^x dt/t`, and `0 ≤ ψ(x)/x ≤ 2`. -/
theorem abs_integral_R_div_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → |∫ t in (2 : ℝ)..x, R t / t ^ 2| ≤ C := by
  obtain ⟨C₀, hC₀, hmert⟩ := mertens
  refine ⟨C₀ + 3, by linarith, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hne : ∀ t ∈ Set.uIcc (2 : ℝ) x, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
  have hRint := Stage4bAux.intervalIntegrable_R_div_sq (a := (2 : ℝ)) (b := x) (by norm_num) hx0
  have h1t : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 x :=
    (ContinuousOn.div continuousOn_const continuousOn_id hne).intervalIntegrable
  have heq : (∫ t in (2 : ℝ)..x, psi t / t ^ 2)
      = (∫ t in (2 : ℝ)..x, R t / t ^ 2) + ∫ t in (2 : ℝ)..x, 1 / t := by
    rw [← intervalIntegral.integral_add hRint h1t]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : t ≠ 0 := hne t ht
    simp only [R]
    field_simp
    ring
  have hlog : (∫ t in (2 : ℝ)..x, 1 / t) = Real.log x - Real.log 2 := by
    rw [integral_one_div (fun h => hne 0 h rfl), Real.log_div hx0.ne' (by norm_num)]
  have hmertx := hmert x hx
  have hpsi1 : (0 : ℝ) ≤ psi x := Stage5Aux.psi_nonneg x
  have hpsi2 : psi x ≤ 2 * x := Stage4aAux.psi_le_two_mul hx0.le
  have hpsidiv : psi x / x ≤ 2 := by
    rw [div_le_iff₀ hx0]; linarith
  have hpsidiv0 : (0 : ℝ) ≤ psi x / x := by positivity
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hval : (∫ t in (2 : ℝ)..x, R t / t ^ 2)
      = ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n) - Real.log x)
        - psi x / x + Real.log 2 := by
    have := integral_psi_div_sq_eq hx
    rw [heq, hlog] at this
    linarith
  rw [hval, abs_le]
  rw [abs_le] at hmertx
  constructor <;> linarith [hmertx.1, hmertx.2]

end Stage4bMertens
end SelbergPNT
