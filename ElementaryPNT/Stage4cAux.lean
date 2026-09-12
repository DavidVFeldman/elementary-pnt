/-
ElementaryPNT.Stage4cAux — auxiliary development for `ElementaryPNT.Stage4c`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage3
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4bAux
import ElementaryPNT.Stage4bGap

open Filter Topology MeasureTheory

namespace SelbergPNT

namespace Stage4cAux

/-! ## From `=O[atTop]` to an explicit constant on `[1,∞)` -/

/-- A function that is `O(x)` at infinity and bounded on every bounded subinterval of `[1,∞)`
satisfies `|f x| ≤ C x` on the whole of `[1,∞)`, for a single constant `C`. -/
theorem const_of_isBigO (f : ℝ → ℝ) (hf : f =O[atTop] fun x : ℝ => x)
    (hloc : ∀ b : ℝ, ∃ M : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ b → |f x| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → |f x| ≤ C * x := by
  obtain ⟨C₀, hC₀⟩ := Asymptotics.isBigO_iff.1 hf
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 hC₀
  obtain ⟨M, hM⟩ := hloc (max b₀ 1)
  refine ⟨max (max C₀ M) 0 + 1, by positivity, fun x hx => ?_⟩
  set C := max (max C₀ M) 0 + 1 with hC
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) ≤ max (max C₀ M) 0 := le_max_right _ _
    simp only [hC]; linarith
  rcases le_total x (max b₀ 1) with h | h
  · have hx' := hM x hx h
    have hMC : M ≤ C - 1 := by
      have : M ≤ max (max C₀ M) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
      simp only [hC]; linarith
    nlinarith
  · have h1 := hb₀ x (le_trans (le_max_left _ _) h)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ x)] at h1
    have hC0C : C₀ ≤ C := by
      have : C₀ ≤ max (max C₀ M) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
      simp only [hC]; linarith
    nlinarith

/-! ## `S` below `2` -/

/-- `ψ` vanishes below `2`, so `R(u)/u = −1` there and `S(t) = 2 − t` for `0 < t ≤ 2`. -/
theorem S_eq_two_sub {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : S t = 2 - t := by
  have hR : ∀ u : ℝ, 0 < u → u < 2 → R u / u = -1 := by
    intro u hu hu2
    have hpsi : psi u = 0 := by
      rcases lt_or_ge u 1 with h | h
      · exact Stage5Aux.psi_eq_zero_of_lt_one h
      · have hfloor : ⌊u⌋₊ = 1 := by
          rw [Nat.floor_eq_iff (by linarith)]
          exact ⟨by exact_mod_cast h, by push_cast; linarith⟩
        simp [psi, hfloor]
    rw [R, hpsi]
    field_simp
    ring
  have hae : ∀ᵐ u : ℝ, u ≠ 2 := by rw [ae_iff]; simp
  have h : (∫ u in (2 : ℝ)..t, R u / u) = ∫ _u in (2 : ℝ)..t, (-1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with u hu hmem
    rw [Set.uIoc_of_ge ht2] at hmem
    exact hR u (lt_of_lt_of_le ht hmem.1.le) (lt_of_le_of_ne hmem.2 hu)
  rw [S, h]
  simp

/-- Consequently `|S t| ≤ 2` for `0 < t ≤ 2`. -/
theorem abs_S_le_two {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) : |S t| ≤ 2 := by
  rw [S_eq_two_sub ht ht2, abs_of_nonneg (by linarith)]
  linarith

/-- A crude bound in the other regime: `|S t| ≤ 2 t` for `t ≥ 1`. -/
theorem abs_S_le_two_mul {t : ℝ} (ht : 1 ≤ t) : |S t| ≤ 2 * t := by
  have h := Stage4aAux.abs_S_le_self ht
  linarith

/-! ## Abel summation and harmonic sums -/

/-- Summation by parts over `Finset.Icc 1 (N+1)`. -/
theorem abel_sum_Icc (a w : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 (N + 1), a m * w m
      = (∑ m ∈ Finset.Icc 1 (N + 1), a m) * w (N + 1)
        + ∑ m ∈ Finset.Icc 1 N, (∑ j ∈ Finset.Icc 1 m, a j) * (w m - w (m + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
      have e1 : ∑ m ∈ Finset.Icc 1 (n + 1 + 1), a m * w m
          = (∑ m ∈ Finset.Icc 1 (n + 1), a m * w m) + a (n + 2) * w (n + 2) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e2 : ∑ m ∈ Finset.Icc 1 (n + 1 + 1), a m
          = (∑ m ∈ Finset.Icc 1 (n + 1), a m) + a (n + 2) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e3 : ∑ m ∈ Finset.Icc 1 (n + 1), (∑ j ∈ Finset.Icc 1 m, a j) * (w m - w (m + 1))
          = (∑ m ∈ Finset.Icc 1 n, (∑ j ∈ Finset.Icc 1 m, a j) * (w m - w (m + 1)))
            + (∑ j ∈ Finset.Icc 1 (n + 1), a j) * (w (n + 1) - w (n + 2)) :=
        Finset.sum_Icc_succ_top (by omega) _
      rw [e1, e2, e3, ih]
      ring

/-- `log(m+1) − log m ≥ 1/(m+1)`, the step of the harmonic comparison. -/
theorem log_succ_sub_log_ge (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1) ≤ Real.log (m + 1) - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h : Real.log ((m : ℝ) / (m + 1)) ≤ (m : ℝ) / (m + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h2 : (m : ℝ) / (m + 1) - 1 = -(1 / (m + 1)) := by field_simp; ring
  rw [h2] at h
  linarith

/-- `∑_{m = 1}^{N} 1/(m+1) ≤ log (N+1)`. -/
theorem sum_one_div_succ_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m + 1) ≤ Real.log (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h := log_succ_sub_log_ge (n + 1) (by omega)
      push_cast at h ⊢
      linarith

/-- `∑_{m = 2}^{N} 1/m² ≤ 1 − 1/N`, by comparison with the telescoping `1/(m(m−1))`. -/
theorem sum_one_div_sq_le' {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 - 1 / N := by
  induction N with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hN with h | h
      · simp [← h]
      · have hn : 1 ≤ n := by omega
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hih := ih hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have e : (1 : ℝ) / n - 1 / ((n : ℝ) + 1) = 1 / (n * ((n : ℝ) + 1)) := by
          field_simp
          ring
        have key : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n * ((n : ℝ) + 1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        push_cast
        rw [← e] at key
        linarith

/-- `∑_{m = 2}^{N} 1/m² ≤ 1`. -/
theorem sum_one_div_sq_le (N : ℕ) : ∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have h1 := sum_one_div_sq_le' h
    have hN : (0 : ℝ) < N := by exact_mod_cast h
    have h2 : (0:ℝ) < 1 / N := by positivity
    linarith

/-! ## Mertens as an upper bound on `[1,∞)` -/

/-- `∑_{n ≤ x} Λ(n)/n ≤ log x + C` for all `x ≥ 1`, from the `mertens`. -/
theorem sum_vonMangoldt_div_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤ Real.log x + C := by
  obtain ⟨C, hC, hb⟩ := mertens
  refine ⟨C, hC, fun x hx => ?_⟩
  rcases lt_or_ge x 2 with h | h
  · have hfloor : ⌊x⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by exact_mod_cast hx, by push_cast; linarith⟩
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [hfloor]
    simp
    linarith
  · have := abs_le.1 (hb x h)
    linarith [this.2]

/-! ## The two stage-10 estimates with explicit constants -/

/-- Selberg's inequality with an explicit constant, valid for all `x ≥ 1`. -/
theorem selberg_first_const : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
    |R x * Real.log x + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n|
      ≤ C * x := by
  obtain ⟨CM, hCM, hM⟩ := sum_vonMangoldt_div_le
  refine const_of_isBigO _ (by simpa only [R] using selberg_first) ?_
  intro b
  refine ⟨(max b 1) * Real.log (max b 1) + (max b 1) * (Real.log (max b 1) + CM),
    fun x hx hxb => ?_⟩
  set B := max b 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hxB : x ≤ B := le_trans hxb (le_max_left _ _)
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogB : Real.log x ≤ Real.log B := Real.log_le_log hx0 hxB
  have h1 : |R x * Real.log x| ≤ x * Real.log x := by
    rw [abs_mul, abs_of_nonneg hlogx]
    exact mul_le_mul_of_nonneg_right (Stage4aAux.abs_R_le_self hx0) hlogx
  have h2 : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n|
      ≤ x * (Real.log x + CM) := by
    have step1 : |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n|
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x / n) * ArithmeticFunction.vonMangoldt n := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n hn => ?_)
      simp only [Finset.mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hxn : (0 : ℝ) < x / n := by positivity
      rw [abs_mul, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
      exact mul_le_mul_of_nonneg_right (Stage4aAux.abs_R_le_self hxn)
        ArithmeticFunction.vonMangoldt_nonneg
    have step2 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x / n) * ArithmeticFunction.vonMangoldt n
        = x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [step2] at step1
    have := hM x hx
    nlinarith [step1, ArithmeticFunction.vonMangoldt_nonneg (n := 1)]
  have := abs_add_le (R x * Real.log x)
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n)
  nlinarith [Real.log_nonneg hB1]

/-- `∑_{m ≤ N} (Λ₂(m) − 2 log m) = O(N)` with an explicit constant, for all `N ≥ 1`. -/
theorem selberg_second_const : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    |∑ m ∈ Finset.Icc 1 N, (Lambda2 m - 2 * Real.log m)| ≤ C * N := by
  have hloc : ∀ b : ℝ, ∃ M : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ b →
      |∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Lambda2 m - 2 * Real.log m)| ≤ M := by
    intro b
    refine ⟨∑ m ∈ Finset.Icc 1 ⌊max b 1⌋₊, |Lambda2 m - 2 * Real.log m|, fun x hx hxb => ?_⟩
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
    exact Finset.Icc_subset_Icc_right (Nat.floor_le_floor (le_trans hxb (le_max_left _ _)))
  obtain ⟨C, hC, h⟩ := const_of_isBigO
    (fun t : ℝ => ∑ m ∈ Finset.Icc 1 ⌊t⌋₊, (Lambda2 m - 2 * Real.log m)) selberg_second' hloc
  refine ⟨C, hC, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have := h (N : ℝ) hNR
  simpa using this

end Stage4cAux

end SelbergPNT
