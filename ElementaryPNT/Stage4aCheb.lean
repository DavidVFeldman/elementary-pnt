/-
ElementaryPNT.Stage4aCheb — auxiliary development for `ElementaryPNT.Stage4a`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib

open Real Filter

namespace SelbergPNT
namespace Stage4aCheb

/-! ## Numerical bounds on logarithms -/

/-- `2.7182818283 ^ p ≤ exp p`, from `Real.exp_one_gt_d9`. -/
theorem d9_pow_le_exp (p : ℕ) : ((2.7182818283 : ℝ)) ^ p ≤ Real.exp p := by
  have h : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  calc ((2.7182818283 : ℝ)) ^ p ≤ (Real.exp 1) ^ p := pow_le_pow_left₀ (by norm_num) h p
    _ = Real.exp p := by rw [← Real.exp_nat_mul]; norm_num

/-- `log N ≤ p / q`, certified by the rational inequality `N ^ q ≤ 2.7182818283 ^ p`. -/
theorem log_le_ratio {N : ℝ} (hN : 0 < N) {p q : ℕ} (hq : 0 < q)
    (h : N ^ q ≤ ((2.7182818283 : ℝ)) ^ p) : Real.log N ≤ (p : ℝ) / q := by
  have h1 : Real.log (N ^ q) ≤ Real.log (Real.exp p) :=
    Real.log_le_log (by positivity) (h.trans (d9_pow_le_exp p))
  rw [Real.log_pow, Real.log_exp] at h1
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [le_div_iff₀ hq']
  linarith

theorem log_six_le : Real.log 6 ≤ 1.8 := by
  have := log_le_ratio (N := (6 : ℝ)) (by norm_num) (p := 9) (q := 5) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_thirty_le : Real.log 30 ≤ 3.5 := by
  have := log_le_ratio (N := (30 : ℝ)) (by norm_num) (p := 7) (q := 2) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_two_ten_le : Real.log 210 ≤ 5.5 := by
  have := log_le_ratio (N := (210 : ℝ)) (by norm_num) (p := 11) (q := 2) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_primorial_twenty_le : Real.log 9699690 ≤ 16.5 := by
  have := log_le_ratio (N := (9699690 : ℝ)) (by norm_num) (p := 33) (q := 2) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_two_le : Real.log 2 ≤ 0.694 := by
  have := Real.log_two_lt_d9
  linarith

theorem log_four_lt : Real.log 4 < 1.3862943616 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  rw [h]; linarith

/-! ## The terms `θ(x^{1/n})` -/

/-- If `x ≤ c ^ n` with `n > 0` then `x ^ (1/n) ≤ c`. -/
theorem rpow_inv_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : x ≤ c ^ n) :
    x ^ ((1 : ℝ) / (n : ℝ)) ≤ c := by
  have h1 : x ^ ((1 : ℝ) / (n : ℝ)) ≤ (c ^ n) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_le_rpow hx h (by positivity)
  have h2 : ((c : ℝ) ^ n) ^ ((1 : ℝ) / (n : ℝ)) = c := by
    rw [← Real.rpow_natCast c n, ← Real.rpow_mul hc]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [mul_one_div, div_self hn', Real.rpow_one]
  linarith [h2 ▸ h1]

/-- `θ t ≤ log (primorial ⌊c⌋)` whenever `t ≤ c`. -/
theorem theta_le_log_primorial {t c : ℝ} (h : t ≤ c) :
    Chebyshev.theta t ≤ Real.log (primorial ⌊c⌋₊) := by
  rw [← Chebyshev.theta_eq_log_primorial]
  exact Chebyshev.theta_mono h

/-- The workhorse: a bound for one term of the sum. -/
theorem theta_rpow_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : x ≤ c ^ n) :
    Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ))) ≤ Real.log (primorial ⌊c⌋₊) :=
  theta_le_log_primorial (rpow_inv_le hx hc hn h)

/-! ## The banded estimate -/

/-- If `2 ≤ x < 2^(M+1)` then `ψ x ≤ (log 4) x + ∑_{n ∈ Icc 2 M} θ(x^{1/n})`. -/
theorem psi_le_theta_add_sum {x : ℝ} (hx : 2 ≤ x) {M : ℕ} (hM : x < 2 ^ (M + 1)) :
    Chebyshev.psi x ≤ Real.log 4 * x +
      ∑ n ∈ Finset.Icc 2 M, Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hKM : ⌊Real.log x / Real.log 2⌋₊ ≤ M := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : Real.log x < ((M : ℝ) + 1) * Real.log 2 := by
      have : Real.log x < Real.log (2 ^ (M + 1)) := Real.log_lt_log hx0 hM
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
    have h2 : Real.log x / Real.log 2 < (M : ℝ) + 1 := by
      rw [div_lt_iff₀ hlog2]; linarith
    have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
    have h3 : ⌊Real.log x / Real.log 2⌋₊ < M + 1 := by
      rw [Nat.floor_lt (div_nonneg hlx hlog2.le)]
      push_cast
      linarith
    omega
  have hsub : Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊ ⊆ Finset.Icc 2 M :=
    Finset.Icc_subset_Icc_right hKM
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
      Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ))) ≤
      ∑ n ∈ Finset.Icc 2 M, Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Chebyshev.theta_nonneg _
  have htheta : Chebyshev.theta x ≤ Real.log 4 * x := Chebyshev.theta_le_log4_mul_x hx0.le
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx]
  linarith

/-! ## The four finite bands -/

theorem psi_le_two_mul_band_D {x : ℝ} (hx : 2 ≤ x) (hx' : x < 4.5) :
    Chebyshev.psi x ≤ 2 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hb := psi_le_theta_add_sum hx (M := 2) (by norm_num; linarith)
  have h2 : Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.2) hx0 (by norm_num) (n := 2) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.2 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.2 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this

  have hicc : Finset.Icc 2 2 = ({2} : Finset ℕ) := rfl
  rw [hicc, Finset.sum_singleton] at hb
  have hl2 := log_two_le
  have hl4 := log_four_lt
  nlinarith [hb, h2, hl2, hl4]

theorem psi_le_two_mul_band_C {x : ℝ} (hx : 4.5 ≤ x) (hx' : x < 12) :
    Chebyshev.psi x ≤ 2 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hb := psi_le_theta_add_sum (by linarith : (2:ℝ) ≤ x) (M := 3) (by norm_num; linarith)
  have h2 : Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ≤ Real.log 6 := by
    have := theta_rpow_le (x := x) (c := 3.5) hx0 (by norm_num) (n := 2) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(3.5 : ℝ)⌋₊ = 6 := by
      rw [show ⌊(3.5 : ℝ)⌋₊ = 3 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h3 : Chebyshev.theta (x ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.3) hx0 (by norm_num) (n := 3) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.3 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.3 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have hicc : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := rfl
  rw [hicc] at hb
  rw [show (∑ n ∈ ({2, 3} : Finset ℕ), Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ)))) =
      Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) +
        Chebyshev.theta (x ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) by simp] at hb
  nlinarith [hb, h2, h3, log_two_le, log_six_le, log_four_lt]

theorem psi_le_two_mul_band_B {x : ℝ} (hx : 12 ≤ x) (hx' : x < 46) :
    Chebyshev.psi x ≤ 2 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hb := psi_le_theta_add_sum (by linarith : (2:ℝ) ≤ x) (M := 5) (by norm_num; linarith)
  have h2 : Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ≤ Real.log 30 := by
    have := theta_rpow_le (x := x) (c := 6.8) hx0 (by norm_num) (n := 2) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(6.8 : ℝ)⌋₊ = 30 := by
      rw [show ⌊(6.8 : ℝ)⌋₊ = 6 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h3 : Chebyshev.theta (x ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) ≤ Real.log 6 := by
    have := theta_rpow_le (x := x) (c := 3.6) hx0 (by norm_num) (n := 3) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(3.6 : ℝ)⌋₊ = 6 := by
      rw [show ⌊(3.6 : ℝ)⌋₊ = 3 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h4 : Chebyshev.theta (x ^ ((1 : ℝ) / ((4 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.7) hx0 (by norm_num) (n := 4) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.7 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.7 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h5 : Chebyshev.theta (x ^ ((1 : ℝ) / ((5 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.2) hx0 (by norm_num) (n := 5) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.2 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.2 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have hicc : Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset ℕ) := rfl
  rw [hicc] at hb
  rw [show (∑ n ∈ ({2, 3, 4, 5} : Finset ℕ), Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ)))) =
      Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) +
        (Chebyshev.theta (x ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) +
          (Chebyshev.theta (x ^ ((1 : ℝ) / ((4 : ℕ) : ℝ))) +
            Chebyshev.theta (x ^ ((1 : ℝ) / ((5 : ℕ) : ℝ))))) by simp] at hb
  nlinarith [hb, h2, h3, h4, h5, log_two_le, log_six_le, log_thirty_le, log_four_lt]

theorem psi_le_two_mul_band_A {x : ℝ} (hx : 46 ≤ x) (hx' : x < 400) :
    Chebyshev.psi x ≤ 2 * x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hb := psi_le_theta_add_sum (by linarith : (2:ℝ) ≤ x) (M := 8) (by norm_num; linarith)
  have h2 : Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) ≤ Real.log 9699690 := by
    have := theta_rpow_le (x := x) (c := 20) hx0 (by norm_num) (n := 2) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(20 : ℝ)⌋₊ = 9699690 := by
      rw [show ⌊(20 : ℝ)⌋₊ = 20 by norm_num]
      decide
    rwa [hfl] at this
  have h3 : Chebyshev.theta (x ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) ≤ Real.log 210 := by
    have := theta_rpow_le (x := x) (c := 7.4) hx0 (by norm_num) (n := 3) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(7.4 : ℝ)⌋₊ = 210 := by
      rw [show ⌊(7.4 : ℝ)⌋₊ = 7 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h4 : Chebyshev.theta (x ^ ((1 : ℝ) / ((4 : ℕ) : ℝ))) ≤ Real.log 6 := by
    have := theta_rpow_le (x := x) (c := 4.5) hx0 (by norm_num) (n := 4) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(4.5 : ℝ)⌋₊ = 6 := by
      rw [show ⌊(4.5 : ℝ)⌋₊ = 4 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h5 : Chebyshev.theta (x ^ ((1 : ℝ) / ((5 : ℕ) : ℝ))) ≤ Real.log 6 := by
    have := theta_rpow_le (x := x) (c := 3.4) hx0 (by norm_num) (n := 5) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(3.4 : ℝ)⌋₊ = 6 := by
      rw [show ⌊(3.4 : ℝ)⌋₊ = 3 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h6 : Chebyshev.theta (x ^ ((1 : ℝ) / ((6 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.8) hx0 (by norm_num) (n := 6) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.8 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.8 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h7 : Chebyshev.theta (x ^ ((1 : ℝ) / ((7 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.4) hx0 (by norm_num) (n := 7) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.4 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.4 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have h8 : Chebyshev.theta (x ^ ((1 : ℝ) / ((8 : ℕ) : ℝ))) ≤ Real.log 2 := by
    have := theta_rpow_le (x := x) (c := 2.2) hx0 (by norm_num) (n := 8) (by norm_num)
      (by norm_num; linarith)
    have hfl : primorial ⌊(2.2 : ℝ)⌋₊ = 2 := by
      rw [show ⌊(2.2 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
      decide
    rwa [hfl] at this
  have hicc : Finset.Icc 2 8 = ({2, 3, 4, 5, 6, 7, 8} : Finset ℕ) := rfl
  rw [hicc] at hb
  rw [show (∑ n ∈ ({2, 3, 4, 5, 6, 7, 8} : Finset ℕ),
        Chebyshev.theta (x ^ ((1 : ℝ) / (n : ℝ)))) =
      Chebyshev.theta (x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) +
        (Chebyshev.theta (x ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) +
          (Chebyshev.theta (x ^ ((1 : ℝ) / ((4 : ℕ) : ℝ))) +
            (Chebyshev.theta (x ^ ((1 : ℝ) / ((5 : ℕ) : ℝ))) +
              (Chebyshev.theta (x ^ ((1 : ℝ) / ((6 : ℕ) : ℝ))) +
                (Chebyshev.theta (x ^ ((1 : ℝ) / ((7 : ℕ) : ℝ))) +
                  Chebyshev.theta (x ^ ((1 : ℝ) / ((8 : ℕ) : ℝ)))))))) by simp] at hb
  nlinarith [hb, h2, h3, h4, h5, h6, h7, h8, log_two_le, log_six_le, log_two_ten_le,
    log_primorial_twenty_le, log_four_lt]

/-! ## The tail `x ≥ 400` -/

theorem psi_le_two_mul_tail {x : ℝ} (hx : 400 ≤ x) : Chebyshev.psi x ≤ 2 * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set t : ℝ := Real.sqrt x with ht
  have ht20 : (20 : ℝ) ≤ t := by
    rw [ht, show (20 : ℝ) = Real.sqrt 400 by
      rw [show (400 : ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have ht0 : (0 : ℝ) < t := by linarith
  have htsq : t ^ 2 = x := Real.sq_sqrt hx0.le
  -- `log t ≤ 2 + t/20`
  have hlog20 : Real.log 20 ≤ 3 := by
    have := log_le_ratio (N := (20 : ℝ)) (by norm_num) (p := 3) (q := 1) (by norm_num)
      (by norm_num)
    norm_num at this ⊢
    linarith
  have hlogt : Real.log t ≤ 2 + t / 20 := by
    have h1 : Real.log (t / 20) ≤ t / 20 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    linarith
  -- `log x = 2 log t`
  have hlogx : Real.log x = 2 * Real.log t := by
    rw [← htsq, Real.log_pow]; push_cast; ring
  have hpsi := Chebyshev.psi_le (x := x) (by linarith)
  rw [← ht] at hpsi
  have hl4 := log_four_lt
  -- `2 t (2 log t) ≤ (2 − log 4) t²`
  have hkey : 2 * t * Real.log x ≤ (2 - Real.log 4) * x := by
    rw [hlogx, ← htsq]
    nlinarith [hlogt, ht20, hl4]
  linarith

/-! ## The bound -/

/-- Chebyshev's upper bound in the form the stage-12 targets need: `ψ(x) ≤ 2x`. -/
theorem psi_le_two_mul {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ 2 * x := by
  rcases lt_or_ge x 2 with h | h
  · rw [Chebyshev.psi_eq_zero_of_lt_two h]; linarith
  rcases lt_or_ge x 4.5 with h1 | h1
  · exact psi_le_two_mul_band_D h h1
  rcases lt_or_ge x 12 with h2 | h2
  · exact psi_le_two_mul_band_C h1 h2
  rcases lt_or_ge x 46 with h3 | h3
  · exact psi_le_two_mul_band_B h2 h3
  rcases lt_or_ge x 400 with h4 | h4
  · exact psi_le_two_mul_band_A h3 h4
  · exact psi_le_two_mul_tail h4

end Stage4aCheb
end SelbergPNT
