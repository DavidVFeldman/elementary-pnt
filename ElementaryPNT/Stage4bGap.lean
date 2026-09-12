/-
ElementaryPNT.Stage4bGap — auxiliary development for `ElementaryPNT.Stage4b`.

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
namespace Stage4bGap

/-! ## The interval `[1,2]`, where `ψ` vanishes -/

/-- `R u / u = −1` for `1 ≤ u < 2`, where `ψ(u) = 0`. -/
theorem R_div_eq_neg_one {u : ℝ} (h1 : 1 ≤ u) (h2 : u < 2) : R u / u = -1 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hfloor : ⌊u⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1, by push_cast; linarith⟩
  have hpsi : psi u = 0 := by simp [psi, hfloor]
  rw [R, hpsi]
  field_simp
  ring

/-- `S(y) = 2 − y` for `1 ≤ y ≤ 2`. -/
theorem S_eq_two_sub {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) : S y = 2 - y := by
  have hae : ∀ᵐ u : ℝ, u ≠ 2 := by
    rw [ae_iff]
    simp
  have h : (∫ u in (2 : ℝ)..y, R u / u) = ∫ _u in (2 : ℝ)..y, (-1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with u hu hmem
    rw [Set.uIoc_of_ge h2] at hmem
    exact R_div_eq_neg_one (by linarith [hmem.1]) (lt_of_le_of_ne hmem.2 hu)
  rw [S, h]
  simp

/-- Below `2` the integral of `S(y)/y²` is at most `1` in absolute value: the integrand lies in
`[0,1]` there and the interval is no longer than `1`. -/
theorem abs_integral_S_div_sq_le_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    |∫ y in a..b, S y / y ^ 2| ≤ 1 := by
  have hbound : ∀ u ∈ Set.uIoc a b, ‖S u / u ^ 2‖ ≤ 1 := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    have hu1 : 1 ≤ u := le_trans ha hu.1.le
    have hu2 : u ≤ 2 := le_trans hu.2 hb
    rw [Real.norm_eq_abs, S_eq_two_sub hu1 hu2, abs_div,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - u),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2), div_le_one (by nlinarith)]
    nlinarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1) hbound
  rw [Real.norm_eq_abs] at h
  have hlen : |b - a| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith

/-! ## The change of variables and the gap bound -/

theorem intervalIntegrable_S_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun y : ℝ => S y / y ^ 2) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  have hsub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro u hu
    rw [Set.uIcc_eq_union] at hu
    rcases hu with hu | hu
    · exact lt_of_lt_of_le (lt_min ha hb) (le_trans (min_le_left a b) hu.1)
    · exact lt_of_lt_of_le (lt_min ha hb) (le_trans (min_le_right a b) hu.1)
  exact (Stage4bAux.continuousOn_S.mono hsub).div (by fun_prop)
    fun u hu => pow_ne_zero 2 (ne_of_gt (hsub hu))

/-- The gap bound in the variable `y`: from a universal bound `C` for `|∫₂^x S(y)/y² dy|` one
gets `2C + 1` for an arbitrary subinterval of `[1,∞)`, splitting at `2`. -/
theorem abs_integral_S_div_sq_le_of_bound {C : ℝ}
    (hbd : ∀ x : ℝ, 2 ≤ x → |∫ y in (2 : ℝ)..x, S y / y ^ 2| ≤ C)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |∫ y in a..b, S y / y ^ 2| ≤ 2 * C + 1 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hbd 2 le_rfl)
  rcases le_or_gt b 2 with hb2 | hb2
  · have := abs_integral_S_div_sq_le_one ha hab hb2
    linarith
  rcases le_or_gt 2 a with ha2 | ha2
  · have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_S_div_sq (a := (2 : ℝ)) (b := a) (by norm_num) (by linarith))
      (intervalIntegrable_S_div_sq (a := a) (b := b) (by linarith) (by linarith))
    have heq : (∫ y in a..b, S y / y ^ 2)
        = (∫ y in (2 : ℝ)..b, S y / y ^ 2) - ∫ y in (2 : ℝ)..a, S y / y ^ 2 := by linarith
    rw [heq]
    have h1 := hbd b (by linarith)
    have h2 := hbd a ha2
    calc |(∫ y in (2 : ℝ)..b, S y / y ^ 2) - ∫ y in (2 : ℝ)..a, S y / y ^ 2|
        ≤ |∫ y in (2 : ℝ)..b, S y / y ^ 2| + |∫ y in (2 : ℝ)..a, S y / y ^ 2| := abs_sub _ _
      _ ≤ 2 * C + 1 := by linarith
  · have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_S_div_sq (a := a) (b := (2 : ℝ)) (by linarith) (by norm_num))
      (intervalIntegrable_S_div_sq (a := (2 : ℝ)) (b := b) (by norm_num) (by linarith))
    have heq : (∫ y in a..b, S y / y ^ 2)
        = (∫ y in a..(2 : ℝ), S y / y ^ 2) + ∫ y in (2 : ℝ)..b, S y / y ^ 2 := by linarith
    rw [heq]
    have h1 := abs_integral_S_div_sq_le_one ha ha2.le le_rfl
    have h2 := hbd b (by linarith)
    calc |(∫ y in a..(2 : ℝ), S y / y ^ 2) + ∫ y in (2 : ℝ)..b, S y / y ^ 2|
        ≤ |∫ y in a..(2 : ℝ), S y / y ^ 2| + |∫ y in (2 : ℝ)..b, S y / y ^ 2| := abs_add_le _ _
      _ ≤ 2 * C + 1 := by linarith

/-- The change of variables `y = eᵛ`: `∫_a^b W(v) dv = ∫_{e^a}^{e^b} S(y)/y² dy`. -/
theorem integral_W_eq (a b : ℝ) :
    (∫ v in a..b, W v) = ∫ y in (Real.exp a)..(Real.exp b), S y / y ^ 2 := by
  have himg : Real.exp '' Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    rintro y ⟨v, -, rfl⟩
    exact Real.exp_pos v
  have hg : ContinuousOn (fun y : ℝ => S y / y ^ 2) (Real.exp '' Set.uIcc a b) :=
    (Stage4bAux.continuousOn_S.mono himg).div (by fun_prop)
      fun u hu => pow_ne_zero 2 (ne_of_gt (himg hu))
  have h := intervalIntegral.integral_comp_smul_deriv'
    (f := Real.exp) (f' := Real.exp) (g := fun y : ℝ => S y / y ^ 2) (a := a) (b := b)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hg
  rw [← h]
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp [W, Function.comp]
  rw [pow_two]
  field_simp

/-! ## The sign of `W` on a gap -/

/-- On an interval where the continuous `W` does not vanish, `W` has constant sign. -/
theorem sign_constant_on_gap {a b : ℝ} (hne : ∀ v : ℝ, a < v → v < b → W v ≠ 0) :
    (∀ v : ℝ, a ≤ v → v ≤ b → 0 ≤ W v) ∨ (∀ v : ℝ, a ≤ v → v ≤ b → W v ≤ 0) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨u, hua, hub, hu⟩, ⟨v, hva, hvb, hv⟩⟩ := hcon
  have hzero : (0 : ℝ) ∈ Set.uIcc (W u) (W v) := Set.mem_uIcc.2 (Or.inl ⟨hu.le, hv.le⟩)
  obtain ⟨w, hw, hw0⟩ := intermediate_value_uIcc
    (Stage4bAux.continuous_W.continuousOn (s := Set.uIcc u v)) hzero
  have hwu : w ≠ u := by rintro rfl; rw [hw0] at hu; exact lt_irrefl 0 hu
  have hwv : w ≠ v := by rintro rfl; rw [hw0] at hv; exact lt_irrefl 0 hv
  rw [Set.mem_uIcc] at hw
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne w (lt_of_le_of_lt hua (lt_of_le_of_ne h1 (Ne.symm hwu)))
      (lt_of_lt_of_le (lt_of_le_of_ne h2 hwv) hvb) hw0
  · exact hne w (lt_of_le_of_lt hva (lt_of_le_of_ne h1 (Ne.symm hwv)))
      (lt_of_lt_of_le (lt_of_le_of_ne h2 hwu) hub) hw0

/-- Hence the integral of `|W|` over such an interval is the absolute value of the integral. -/
theorem integral_abs_W_eq_abs_integral {a b : ℝ} (hab : a < b)
    (hne : ∀ v : ℝ, a < v → v < b → W v ≠ 0) :
    (∫ v in a..b, |W v|) = |∫ v in a..b, W v| := by
  rcases sign_constant_on_gap hne with hsign | hsign
  · have h1 : (∫ v in a..b, |W v|) = ∫ v in a..b, W v := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hab.le] at hv
      exact abs_of_nonneg (hsign v hv.1 hv.2)
    rw [h1, abs_of_nonneg (intervalIntegral.integral_nonneg hab.le fun v hv => hsign v hv.1 hv.2)]
  · have h1 : (∫ v in a..b, |W v|) = ∫ v in a..b, -W v := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hab.le] at hv
      exact abs_of_nonpos (hsign v hv.1 hv.2)
    have h2 : (∫ v in a..b, W v) ≤ 0 := by
      have h3 : (0 : ℝ) ≤ ∫ v in a..b, -W v :=
        intervalIntegral.integral_nonneg (μ := volume) hab.le
          fun v hv => neg_nonneg.2 (hsign v hv.1 hv.2)
      rw [intervalIntegral.integral_neg] at h3
      linarith
    rw [h1, intervalIntegral.integral_neg, abs_of_nonpos h2]

end Stage4bGap
end SelbergPNT
