/-
ElementaryPNT.Stage4cStep4 — auxiliary development for `ElementaryPNT.Stage4c`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4bAux
import ElementaryPNT.Stage4cAux
import ElementaryPNT.Stage4cStep3

open Filter Topology MeasureTheory

namespace SelbergPNT

namespace Stage4cStep4

/-! ## The integrand -/

/-- The integrand `u ↦ |S(y/u)| log u` is continuous away from the origin. -/
theorem continuousOn_integrand (y : ℝ) (hy : 0 < y) {s : Set ℝ} (hs : s ⊆ Set.Ioi (0:ℝ)) :
    ContinuousOn (fun u : ℝ => |S (y / u)| * Real.log u) s := by
  have h1 : ContinuousOn (fun u : ℝ => S (y / u)) s := by
    refine Stage4bAux.continuousOn_S.comp (by fun_prop (disch := intro u hu; exact ne_of_gt (hs hu))) ?_
    intro u hu
    have hu0 : 0 < u := hs hu
    simp only [Set.mem_Ioi]
    positivity
  exact (h1.abs).mul (Real.continuousOn_log.mono fun u hu => ne_of_gt (hs hu))

/-- The integrand is interval integrable away from the origin. -/
theorem intervalIntegrable_integrand (y : ℝ) (hy : 0 < y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => |S (y / u)| * Real.log u) volume a b := by
  refine ContinuousOn.intervalIntegrable (continuousOn_integrand y hy ?_)
  intro u hu
  refine lt_of_lt_of_le (lt_min ha hb) ?_
  rw [Set.uIcc_eq_union] at hu
  rcases hu with hu | hu
  · exact le_trans (min_le_left a b) hu.1
  · exact le_trans (min_le_right a b) hu.1

/-! ## Comparing the sum with the integral -/

/-- `log a ≤ ∫_a^{a+1} log u du ≤ log (a+1)` for `a ≥ 1`. -/
theorem integral_log_bounds {a : ℝ} (ha : 1 ≤ a) :
    Real.log a ≤ (∫ u in a..(a+1), Real.log u) ∧
      (∫ u in a..(a+1), Real.log u) ≤ Real.log (a + 1) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hint : IntervalIntegrable Real.log volume a (a + 1) := by
    refine ContinuousOn.intervalIntegrable (Real.continuousOn_log.mono ?_)
    rw [Set.uIcc_of_le (by linarith)]
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le ha0 hu.1)
  constructor
  · have := intervalIntegral.integral_mono_on (a := a) (b := a + 1) (by linarith)
      intervalIntegrable_const hint (g := Real.log) (f := fun _ => Real.log a)
      (fun u hu => Real.log_le_log ha0 hu.1)
    simpa using this
  · have := intervalIntegral.integral_mono_on (a := a) (b := a + 1) (by linarith)
      hint intervalIntegrable_const (f := Real.log) (g := fun _ => Real.log (a + 1))
      (fun u hu => Real.log_le_log (lt_of_lt_of_le ha0 hu.1) hu.2)
    simpa using this

/-- The comparison on a single interval `[m, m+1]`. -/
theorem term_le (y : ℝ) (hy : 2 ≤ y) (m : ℕ) (hm2 : 2 ≤ m) (hmy : (m : ℝ) ≤ y) :
    |S (y / m)| * Real.log m ≤ (∫ u in (m:ℝ)..((m:ℝ)+1), |S (y / u)| * Real.log u)
      + (y / m - y / ((m:ℝ)+1)) * Real.log y
      + 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hm0 : (0:ℝ) < m := by
    have : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
    linarith
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by
    have : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
    linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  set d : ℝ := y / m - y / ((m:ℝ)+1) with hd
  have hd0 : 0 ≤ d := by
    rw [hd, sub_nonneg]
    gcongr
    linarith
  have hdle : d ≤ y / m := by
    rw [hd]
    have : 0 ≤ y / ((m:ℝ)+1) := by positivity
    linarith
  have hym1 : (1:ℝ) ≤ y / m := by
    rw [le_div_iff₀ hm0]; linarith
  set c : ℝ := |S (y / m)| - d with hc
  -- the pointwise lower bound on `[m, m+1]`
  have hpt : ∀ u ∈ Set.Icc (m:ℝ) ((m:ℝ)+1), c * Real.log u ≤ |S (y / u)| * Real.log u := by
    intro u hu
    have hu0 : (0:ℝ) < u := lt_of_lt_of_le hm0 hu.1
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg (le_trans hm1 hu.1)
    have hdiff : |S (y / m) - S (y / u)| ≤ |y / m - y / u| :=
      Stage4aAux.abs_S_sub_le (by positivity) (by positivity)
    have hyu1 : y / u ≤ y / m := div_le_div_of_nonneg_left (le_of_lt hy0) hm0 hu.1
    have hyu2 : y / ((m:ℝ)+1) ≤ y / u := div_le_div_of_nonneg_left (le_of_lt hy0) hu0 hu.2
    have hle : |y / m - y / u| ≤ d := by
      rw [abs_of_nonneg (by linarith)]
      rw [hd]
      linarith
    have : c ≤ |S (y / u)| := by
      have h1 : |S (y / m)| - |S (y / u)| ≤ |S (y / m) - S (y / u)| := abs_sub_abs_le_abs_sub _ _
      rw [hc]
      linarith
    exact mul_le_mul_of_nonneg_right this hlogu
  have hintc : IntervalIntegrable (fun u : ℝ => c * Real.log u) volume (m:ℝ) ((m:ℝ)+1) := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine ContinuousOn.mul continuousOn_const (Real.continuousOn_log.mono ?_)
    rw [Set.uIcc_of_le (by linarith)]
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le hm0 hu.1)
  have hintf := intervalIntegrable_integrand y hy0 (a := (m:ℝ)) (b := (m:ℝ)+1) hm0 (by linarith)
  have hmono := intervalIntegral.integral_mono_on (by linarith : (m:ℝ) ≤ (m:ℝ)+1)
    hintc hintf hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  obtain ⟨hL1, hL2⟩ := integral_log_bounds hm1
  set L : ℝ := ∫ u in (m:ℝ)..((m:ℝ)+1), Real.log u with hL
  -- `c L ≥ |S(y/m)| log m − d log y − 3 (y/m) (log(m+1) − log m)`
  have hcabs : |c| ≤ 3 * (y / m) := by
    have h1 : |S (y / m)| ≤ 2 * (y / m) := Stage4cAux.abs_S_le_two_mul hym1
    have h2 : (0:ℝ) ≤ |S (y / m)| := abs_nonneg _
    rw [hc]
    rw [abs_le]
    constructor <;> linarith
  have hLm : 0 ≤ L - Real.log m := by linarith
  have hLm2 : L - Real.log m ≤ Real.log ((m:ℝ)+1) - Real.log m := by linarith
  have hkey : c * L ≥ c * Real.log m - 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m) := by
    have h1 : c * L = c * Real.log m + c * (L - Real.log m) := by ring
    have h2 : |c * (L - Real.log m)| ≤ 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m) := by
      rw [abs_mul, abs_of_nonneg hLm]
      exact mul_le_mul hcabs hLm2 hLm (by positivity)
    have h3 := abs_le.1 h2
    linarith
  have hdlog : d * Real.log m ≤ d * Real.log y :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hm0 hmy) hd0
  have hcm : c * Real.log m = |S (y / m)| * Real.log m - d * Real.log m := by rw [hc]; ring
  linarith [hmono, hkey, hdlog]

/-- Adjacent intervals telescope. -/
theorem sum_integral_adjacent (y : ℝ) (hy : 0 < y) :
    ∀ K : ℕ, 2 ≤ K →
      ∑ m ∈ Finset.Icc 2 K, (∫ u in (m:ℝ)..((m:ℝ)+1), |S (y / u)| * Real.log u)
        = ∫ u in (2:ℝ)..((K:ℝ)+1), |S (y / u)| * Real.log u := by
  intro K
  induction K with
  | zero => omega
  | succ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn' : n = 1 := by omega
        subst hn'
        norm_num
      · rw [Finset.sum_Icc_succ_top (by omega), ih hn2]
        have h1 : (0:ℝ) < 2 := by norm_num
        have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
        have e1 := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_integrand y hy (a := (2:ℝ)) (b := (n:ℝ)+1) h1 (by linarith))
          (intervalIntegrable_integrand y hy (a := (n:ℝ)+1) (b := ((n:ℝ)+1)+1)
            (by linarith) (by linarith))
        have hc : (((n + 1 : ℕ)) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
        rw [hc]
        rw [← e1]

/-- Replacing the sum by an integral:
`∑_{m ≤ y} |S(y/m)| log m ≤ ∫₂^y |S(y/u)| log u du + O(y log y)`. -/
theorem sum_le_integral : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
    (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, |S (y / m)| * Real.log m)
      ≤ (∫ u in (2 : ℝ)..y, |S (y / u)| * Real.log u) + C * y * Real.log y := by
  refine ⟨9, by norm_num, fun y hy => ?_⟩
  have hy0 : (0:ℝ) < y := by linarith
  have hlog2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlog0 : (0:ℝ) < Real.log y := by linarith
  set M := ⌊y⌋₊ with hM
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hy : ((2:ℕ):ℝ) ≤ y)
  have hMy : (M : ℝ) ≤ y := Nat.floor_le (le_of_lt hy0)
  have hyM : y < (M : ℝ) + 1 := Nat.lt_floor_add_one y
  -- drop the term `m = 1`
  have hdrop : ∑ m ∈ Finset.Icc 1 M, |S (y / m)| * Real.log m
      = ∑ m ∈ Finset.Icc 2 M, |S (y / m)| * Real.log m := by
    rw [show Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.sum_insert (by simp)]
    norm_num
  rw [hdrop]
  -- the termwise comparison
  have hterm : ∀ m ∈ Finset.Icc 2 M, |S (y / m)| * Real.log m
      ≤ (∫ u in (m:ℝ)..((m:ℝ)+1), |S (y / u)| * Real.log u)
        + (y / m - y / ((m:ℝ)+1)) * Real.log y
        + 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hmy : (m:ℝ) ≤ y := le_trans (by exact_mod_cast hm.2) hMy
    exact term_le y hy m hm.1 hmy
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_integral_adjacent y hy0 M hM2] at hsum
  -- the two error families
  have herr1 : ∑ m ∈ Finset.Icc 2 M, (y / m - y / ((m:ℝ)+1)) * Real.log y ≤ y * Real.log y := by
    have hb : ∀ m ∈ Finset.Icc 2 M, (y / m - y / ((m:ℝ)+1)) * Real.log y
        ≤ (y * Real.log y) * (1 / (m:ℝ)^2) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      have hm0 : (0:ℝ) < m := by
        have : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
        linarith
      have hne : (m:ℝ) ≠ 0 := ne_of_gt hm0
      have he : y / m - y / ((m:ℝ)+1) = y / ((m:ℝ) * ((m:ℝ)+1)) := by
        field_simp
        ring
      rw [he]
      have hle : y / ((m:ℝ) * ((m:ℝ)+1)) ≤ y * (1 / (m:ℝ)^2) := by
        rw [div_le_iff₀ (by positivity)]
        have : y * (1 / (m:ℝ)^2) * ((m:ℝ) * ((m:ℝ)+1)) = y * (((m:ℝ)+1)/(m:ℝ)) := by
          field_simp
        rw [this]
        have h1 : (1:ℝ) ≤ ((m:ℝ)+1)/(m:ℝ) := by
          rw [le_div_iff₀ hm0]; linarith
        nlinarith
      nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ y)]
    calc ∑ m ∈ Finset.Icc 2 M, (y / m - y / ((m:ℝ)+1)) * Real.log y
        ≤ ∑ m ∈ Finset.Icc 2 M, (y * Real.log y) * (1 / (m:ℝ)^2) := Finset.sum_le_sum hb
      _ = (y * Real.log y) * ∑ m ∈ Finset.Icc 2 M, (1 : ℝ) / (m:ℝ)^2 := by rw [Finset.mul_sum]
      _ ≤ (y * Real.log y) * 1 :=
          mul_le_mul_of_nonneg_left (Stage4cAux.sum_one_div_sq_le M) (by positivity)
      _ = y * Real.log y := by ring
  have herr2 : ∑ m ∈ Finset.Icc 2 M, 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m)
      ≤ 3 * y := by
    have hb : ∀ m ∈ Finset.Icc 2 M, 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m)
        ≤ (3 * y) * (1 / (m:ℝ)^2) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      have hm0 : (0:ℝ) < m := by
        have : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
        linarith
      have hlog : Real.log ((m:ℝ)+1) - Real.log m ≤ 1 / (m:ℝ) := by
        have h := Real.log_le_sub_one_of_pos (x := ((m:ℝ)+1)/(m:ℝ)) (by positivity)
        rw [Real.log_div (by positivity) (ne_of_gt hm0)] at h
        have hne : (m:ℝ) ≠ 0 := ne_of_gt hm0
        have he : ((m:ℝ)+1)/(m:ℝ) - 1 = 1 / (m:ℝ) := by
          rw [add_div, div_self hne]
          ring
        rw [he] at h
        exact h
      have hy3 : (0:ℝ) ≤ 3 * (y / m) := by positivity
      calc 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m)
          ≤ 3 * (y / m) * (1 / (m:ℝ)) := mul_le_mul_of_nonneg_left hlog hy3
        _ = (3 * y) * (1 / (m:ℝ)^2) := by
            have hne : (m:ℝ) ≠ 0 := ne_of_gt hm0
            field_simp
    calc ∑ m ∈ Finset.Icc 2 M, 3 * (y / m) * (Real.log ((m:ℝ)+1) - Real.log m)
        ≤ ∑ m ∈ Finset.Icc 2 M, (3 * y) * (1 / (m:ℝ)^2) := Finset.sum_le_sum hb
      _ = (3 * y) * ∑ m ∈ Finset.Icc 2 M, (1 : ℝ) / (m:ℝ)^2 := by rw [Finset.mul_sum]
      _ ≤ (3 * y) * 1 := mul_le_mul_of_nonneg_left (Stage4cAux.sum_one_div_sq_le M) (by positivity)
      _ = 3 * y := by ring
  -- the tail of the integral, from `y` to `M+1`
  have htail : (∫ u in (2:ℝ)..((M:ℝ)+1), |S (y / u)| * Real.log u)
      ≤ (∫ u in (2 : ℝ)..y, |S (y / u)| * Real.log u) + 2 * y := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_integrand y hy0 (a := (2:ℝ)) (b := y) (by norm_num) hy0)
      (intervalIntegrable_integrand y hy0 (a := y) (b := (M:ℝ)+1) hy0 (by linarith))
    have hbound : |∫ u in y..((M:ℝ)+1), |S (y / u)| * Real.log u| ≤ 2 * y := by
      have hnorm : ∀ u ∈ Set.uIoc y ((M:ℝ)+1), ‖|S (y / u)| * Real.log u‖ ≤ 2 * y := by
        intro u hu
        rw [Set.uIoc_of_le (le_of_lt hyM)] at hu
        have hu1 : y < u := hu.1
        have hu2 : u ≤ (M:ℝ) + 1 := hu.2
        have hu0 : (0:ℝ) < u := lt_of_lt_of_le hy0 hu1.le
        have huy : y / u ≤ 1 := by
          rw [div_le_one hu0]; exact hu1.le
        have hS : |S (y / u)| ≤ 2 := Stage4cAux.abs_S_le_two (by positivity) (by linarith)
        have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
        have hlogle : Real.log u ≤ y := by
          have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
          linarith
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg _), abs_of_nonneg hlogu]
        nlinarith [abs_nonneg (S (y / u))]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := (M:ℝ)+1)
        (C := 2 * y) hnorm
      rw [Real.norm_eq_abs] at h
      have hlen : |(M:ℝ) + 1 - y| ≤ 1 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      nlinarith [abs_nonneg (∫ u in y..((M:ℝ)+1), |S (y / u)| * Real.log u), hy0]
    have := abs_le.1 hbound
    linarith [hsplit]
  have hfin : 3 * y ≤ 5 * y * Real.log y := by nlinarith
  have hfin2 : 2 * y ≤ 3 * y * Real.log y := by nlinarith
  linarith [hsum, herr1, herr2, htail]

/-- (chapter step S4.1d). There is `C₄ > 0` with

  `|S(y)|(log y)² ≤ 2 ∫₂^y |S(y/u)| log u du + C₄ y log y`  for `y ≥ 2`. -/
theorem abs_S_log_sq_le_integral : ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ y : ℝ, 2 ≤ y →
    |S y| * (Real.log y) ^ 2 ≤
      2 * (∫ u in (2 : ℝ)..y, |S (y / u)| * Real.log u) + C₄ * y * Real.log y := by
  obtain ⟨C₃, hC₃, h3⟩ := Stage4cStep3.abs_S_log_sq_le_sum
  obtain ⟨C, hC, hint⟩ := sum_le_integral
  refine ⟨C₃ + 2 * C, by linarith, fun y hy => ?_⟩
  have h1 := h3 y hy
  have h2 := hint y hy
  nlinarith [h1, h2]

/-! ## R14-5: the exponential change of variables -/

/-- The substitution `u = e^{x−v}`, for a function continuous on `(0,∞)`. -/
theorem integral_exp_sub_smul (x : ℝ) (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Ioi 0)) :
    (∫ v in (0:ℝ)..(x - Real.log 2), (-Real.exp (x - v)) • g (Real.exp (x - v)))
      = ∫ u in Real.exp x..(2:ℝ), g u := by
  have hderiv : ∀ v ∈ Set.Ioo (min (0:ℝ) (x - Real.log 2)) (max (0:ℝ) (x - Real.log 2)),
      HasDerivWithinAt (fun v : ℝ => Real.exp (x - v)) (-Real.exp (x - v)) (Set.Ioi v) v := by
    intro v _
    have h : HasDerivAt (fun v : ℝ => x - v) (-1) v := by
      simpa using (hasDerivAt_const v x).sub (hasDerivAt_id v)
    have h2 : HasDerivAt (fun v : ℝ => Real.exp (x - v)) (-Real.exp (x - v)) v := by
      simpa using (Real.hasDerivAt_exp (x - v)).comp v h
    exact h2.hasDerivWithinAt
  have hgc : ContinuousOn g ((fun v : ℝ => Real.exp (x - v)) '' Set.uIcc 0 (x - Real.log 2)) := by
    refine hg.mono ?_
    rintro u ⟨v, _, rfl⟩
    exact Real.exp_pos _
  have h := intervalIntegral.integral_comp_smul_deriv'' (a := (0:ℝ)) (b := x - Real.log 2)
    (f := fun v : ℝ => Real.exp (x - v)) (f' := fun v : ℝ => -Real.exp (x - v)) (g := g)
    (by fun_prop) hderiv (by fun_prop) hgc
  simpa [Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_sub] using h

/-- The change of variables `u = e^{x−v}` in the integral of R14-4, at `y = eˣ`:

  `∫₂^{eˣ} |S(eˣ/u)| log u du = eˣ ∫_0^{x − log 2} |W(v)| (x − v) dv`. -/
theorem integral_substitution (x : ℝ) :
    (∫ u in (2 : ℝ)..Real.exp x, |S (Real.exp x / u)| * Real.log u)
      = Real.exp x * ∫ v in (0 : ℝ)..(x - Real.log 2), |W v| * (x - v) := by
  have hcont : ContinuousOn (fun u : ℝ => |S (Real.exp x / u)| * Real.log u) (Set.Ioi 0) :=
    continuousOn_integrand (Real.exp x) (Real.exp_pos x) (le_refl _)
  have h := integral_exp_sub_smul x (fun u : ℝ => |S (Real.exp x / u)| * Real.log u) hcont
  have hLHS : (∫ v in (0:ℝ)..(x - Real.log 2), (-Real.exp (x - v)) •
      (|S (Real.exp x / Real.exp (x - v))| * Real.log (Real.exp (x - v))))
      = -(Real.exp x * ∫ v in (0:ℝ)..(x - Real.log 2), |W v| * (x - v)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun v _ => ?_
    have hdiv : Real.exp x / Real.exp (x - v) = Real.exp v := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have hW : |S (Real.exp v)| = Real.exp v * |W v| := by
      rw [W, abs_div, abs_of_pos (Real.exp_pos v)]
      field_simp
    have hexp : Real.exp (x - v) * Real.exp v = Real.exp x := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [smul_eq_mul, hdiv, Real.log_exp, hW]
    rw [← hexp]
    ring
  rw [hLHS] at h
  have hsymm : (∫ u in Real.exp x..(2:ℝ), |S (Real.exp x / u)| * Real.log u)
      = -∫ u in (2:ℝ)..Real.exp x, |S (Real.exp x / u)| * Real.log u :=
    intervalIntegral.integral_symm _ _
  rw [hsymm] at h
  linarith

/-- (chapter step S4.1), the blueprint's `W_le_average`:

  `|W(x)| ≤ (2/x²) ∫₀^x |W(v)|(x − v) dv + K/x`  eventually. -/
theorem W_le_average : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
    |W x| ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, |W v| * (x - v)) + K / x := by
  obtain ⟨C₄, hC₄, h4⟩ := abs_S_log_sq_le_integral
  refine ⟨C₄, hC₄, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hlog2 : Real.log 2 ≤ x := by
    have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hexp2 : (2:ℝ) ≤ Real.exp x := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]
    exact Real.exp_le_exp.2 hlog2
  have hmain := h4 (Real.exp x) hexp2
  rw [Real.log_exp] at hmain
  rw [integral_substitution x] at hmain
  -- extend the range of integration from `[0, x − log 2]` to `[0, x]`
  have hnonneg : ∀ v ∈ Set.Icc (0:ℝ) x, 0 ≤ |W v| * (x - v) := by
    intro v hv
    have : 0 ≤ x - v := by linarith [hv.2]
    positivity
  have hintW : ∀ a b : ℝ, IntervalIntegrable (fun v : ℝ => |W v| * (x - v)) volume a b := by
    intro a b
    exact ((Stage4bAux.continuous_W.abs.mul (by fun_prop)).continuousOn).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hintW 0 (x - Real.log 2)) (hintW (x - Real.log 2) x)
  have htail : 0 ≤ ∫ v in (x - Real.log 2)..x, |W v| * (x - v) := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]) ?_
    intro v hv
    have : 0 ≤ x - v := by linarith [hv.2]
    positivity
  have hle : (∫ v in (0:ℝ)..(x - Real.log 2), |W v| * (x - v))
      ≤ ∫ v in (0:ℝ)..x, |W v| * (x - v) := by linarith
  -- divide by `eˣ x²`
  have hSW : |S (Real.exp x)| = Real.exp x * |W x| := by
    rw [W, abs_div, abs_of_pos (Real.exp_pos x)]
    field_simp
  rw [hSW] at hmain
  have hexp0 : (0:ℝ) < Real.exp x := Real.exp_pos x
  have hstep : Real.exp x * |W x| * x ^ 2
      ≤ 2 * (Real.exp x * ∫ v in (0:ℝ)..x, |W v| * (x - v)) + C₄ * Real.exp x * x := by
    have h2 : Real.exp x * (∫ v in (0:ℝ)..(x - Real.log 2), |W v| * (x - v))
        ≤ Real.exp x * ∫ v in (0:ℝ)..x, |W v| * (x - v) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hexp0)
    linarith [hmain]
  rw [← sub_nonneg]
  have hdiv : (2 / x ^ 2) * (∫ v in (0:ℝ)..x, |W v| * (x - v)) + C₄ / x - |W x|
      = (2 * (Real.exp x * ∫ v in (0:ℝ)..x, |W v| * (x - v)) + C₄ * Real.exp x * x
          - Real.exp x * |W x| * x ^ 2) / (Real.exp x * x ^ 2) := by
    field_simp
  rw [hdiv]
  have hpos : (0:ℝ) < Real.exp x * x ^ 2 := by positivity
  exact div_nonneg (by linarith) (le_of_lt hpos)

end Stage4cStep4

end SelbergPNT
