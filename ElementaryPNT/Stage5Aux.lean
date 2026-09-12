/-
ElementaryPNT.Stage5Aux — auxiliary development for `ElementaryPNT.Stage5`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1

open Filter Topology MeasureTheory Asymptotics

namespace SelbergPNT
namespace Stage5Aux

/-- `psi` is monotone (an earlier stage identifies it with Mathlib's `Chebyshev.psi`). -/
theorem psi_mono : Monotone psi := by
  intro x y hxy
  rw [ElementaryPNT.psi_eq_chebyshevPsi, ElementaryPNT.psi_eq_chebyshevPsi]
  exact Chebyshev.psi_mono hxy

/-- `u ↦ R u / u` is interval integrable away from the origin: `psi` is monotone, hence
locally integrable, and `u ↦ 1/u` is continuous there. -/
theorem intervalIntegrable_R_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => R u / u) volume a b := by
  have hpos : ∀ u : ℝ, u ∈ Set.uIcc a b → u ≠ 0 := by
    intro u hu
    refine ne_of_gt (lt_of_lt_of_le (lt_min ha hb) ?_)
    rw [Set.uIcc_eq_union] at hu
    rcases hu with hu | hu
    · exact le_trans (min_le_left a b) hu.1
    · exact le_trans (min_le_right a b) hu.1
  have h1 : IntervalIntegrable psi volume a b :=
    (psi_mono.monotoneOn (Set.uIcc a b)).intervalIntegrable
  have h2 : IntervalIntegrable (fun u : ℝ => psi u * (1 / u)) volume a b :=
    h1.mul_continuousOn (ContinuousOn.div continuousOn_const continuousOn_id hpos)
  refine IntervalIntegrable.congr (f := fun u : ℝ => psi u * (1 / u) - 1) ?_ (h2.sub
    (intervalIntegrable_const (c := (1 : ℝ))))
  intro u hu
  have hu0 : u ≠ 0 := hpos u (Set.uIoc_subset_uIcc hu)
  simp only [R]
  field_simp

/-- Additivity of `S`: `S b − S a = ∫_a^b R(u)/u du` for `2 ≤ a` and `2 ≤ b`. -/
theorem S_sub_S {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    S b - S a = ∫ u in a..b, R u / u := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_R_div (a := (2 : ℝ)) (b := a) (by norm_num) (by linarith))
    (intervalIntegrable_R_div (a := a) (b := b) (by linarith) (by linarith))
  rw [S, S, ← h]
  ring

/-- For a fixed ratio `c`, the increment of `S` over `[y, cy]`, divided by `y`, tends to `0`.
This is the only way the hypothesis `S(x)/x → 0` enters the smoothing argument. -/
theorem S_diff_div_tendsto (hS : Tendsto (fun x : ℝ => S x / x) atTop (𝓝 0)) {c : ℝ}
    (hc : 0 < c) : Tendsto (fun y : ℝ => (S (c * y) - S y) / y) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => S (c * y) / (c * y)) atTop (𝓝 0) :=
    hS.comp (Filter.Tendsto.const_mul_atTop hc tendsto_id)
  have h2 : Tendsto (fun y : ℝ => c * (S (c * y) / (c * y)) - S y / y) atTop (𝓝 0) := by
    simpa using (h1.const_mul c).sub hS
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp

/-- `ψ` vanishes below `1`. -/
theorem psi_eq_zero_of_lt_one {x : ℝ} (hx : x < 1) : psi x = 0 := by
  simp [psi, Nat.floor_eq_zero.2 hx]

theorem psi_nonneg (x : ℝ) : 0 ≤ psi x := by
  rw [ElementaryPNT.psi_eq_chebyshevPsi]
  exact Chebyshev.psi_nonneg x

/-- `ψ(x)/x` is globally nonnegative. -/
theorem psi_div_nonneg (x : ℝ) : 0 ≤ psi x / x := by
  rcases lt_or_ge x 1 with hx | hx
  · rw [psi_eq_zero_of_lt_one hx]; simp
  · exact div_nonneg (psi_nonneg x) (by linarith)

/-- `ψ(x)/x` is globally bounded above, by Chebyshev. -/
theorem psi_div_le_const (x : ℝ) : psi x / x ≤ Real.log 4 + 4 := by
  have hc : (0 : ℝ) < Real.log 4 + 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  rcases lt_or_ge x 1 with hx | hx
  · rw [psi_eq_zero_of_lt_one hx, zero_div]
    exact hc.le
  · rw [ElementaryPNT.psi_eq_chebyshevPsi, div_le_iff₀ (by linarith)]
    exact Chebyshev.psi_le_const_mul_self (by linarith)

theorem psi_div_isBoundedUnder : IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => psi x / x) :=
  isBoundedUnder_of ⟨Real.log 4 + 4, psi_div_le_const⟩

theorem psi_div_isBoundedUnder_ge : IsBoundedUnder (· ≥ ·) atTop (fun x : ℝ => psi x / x) :=
  isBoundedUnder_of ⟨0, psi_div_nonneg⟩

/-- The `limsup` half of the smoothing argument (R11-7): over `[y, y(1+ε)]` the monotonicity of
`ψ` turns the smallness of the increment of `S` into an upper bound for `ψ(y)/y`. -/
theorem limsup_psi_div_le_one (hS : Tendsto (fun x : ℝ => S x / x) atTop (𝓝 0)) :
    limsup (fun x : ℝ => psi x / x) atTop ≤ 1 := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hcpos : (0 : ℝ) < 1 + ε := by linarith
  have hΔ := S_diff_div_tendsto hS hcpos
  have hg : Tendsto (fun y : ℝ => (1 + ε) * (1 + (S ((1 + ε) * y) - S y) / y / ε)) atTop
      (𝓝 (1 + ε)) := by
    have h1 : Tendsto (fun y : ℝ => 1 + (S ((1 + ε) * y) - S y) / y / ε) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (hΔ.div_const ε)
    simpa using h1.const_mul (1 + ε)
  have hev : ∀ᶠ y : ℝ in atTop,
      psi y / y ≤ (1 + ε) * (1 + (S ((1 + ε) * y) - S y) / y / ε) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hylt : y < (1 + ε) * y := by nlinarith
    have hmono : ∀ u : ℝ, u ∈ Set.Icc y ((1 + ε) * y) →
        psi y / ((1 + ε) * y) - 1 ≤ R u / u := by
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hy0 hu.1
      have hden : (0 : ℝ) < (1 + ε) * y := by positivity
      have hle : psi y / ((1 + ε) * y) ≤ psi u / u := by
        rw [div_le_div_iff₀ hden hu0]
        nlinarith [psi_mono hu.1, hu.2, psi_nonneg y, psi_nonneg u, hu0, hy0]
      have hR : R u / u = psi u / u - 1 := by
        simp only [R]
        field_simp
      rw [hR]
      linarith
    have hint := intervalIntegral.integral_mono_on hylt.le
      (intervalIntegrable_const (c := psi y / ((1 + ε) * y) - 1))
      (intervalIntegrable_R_div hy0 (by positivity)) hmono
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    rw [← S_sub_S hy (by nlinarith)] at hint
    have hεy : (0 : ℝ) < ε * y := by positivity
    have hkey : psi y / ((1 + ε) * y) - 1 ≤ (S ((1 + ε) * y) - S y) / (ε * y) := by
      rw [le_div_iff₀ hεy]
      nlinarith [hint]
    have hexp : (S ((1 + ε) * y) - S y) / y / ε = (S ((1 + ε) * y) - S y) / (ε * y) := by
      field_simp
      try ring
    have hdiv : psi y / ((1 + ε) * y) = psi y / y / (1 + ε) := by
      field_simp
      try ring
    rw [hdiv] at hkey
    rw [hexp]
    have hcalc : psi y / y = (1 + ε) * (psi y / y / (1 + ε)) := by field_simp
    rw [hcalc]
    have := mul_le_mul_of_nonneg_left (show psi y / y / (1 + ε) ≤
      1 + (S ((1 + ε) * y) - S y) / (ε * y) by linarith) hcpos.le
    linarith
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun x : ℝ => psi x / x) :=
    isCoboundedUnder_le_of_eventually_le atTop (x := 0)
      (Eventually.of_forall psi_div_nonneg)
  calc limsup (fun x : ℝ => psi x / x) atTop
      ≤ limsup (fun y : ℝ => (1 + ε) * (1 + (S ((1 + ε) * y) - S y) / y / ε)) atTop :=
        limsup_le_limsup hev hcob hg.isBoundedUnder_le
    _ = 1 + ε := hg.limsup_eq

/-- The `liminf` half of the smoothing argument (R11-7), the chapter's exercise: the same
comparison on `[y(1−ε), y]`. -/
theorem one_le_liminf_psi_div (hS : Tendsto (fun x : ℝ => S x / x) atTop (𝓝 0)) :
    1 ≤ liminf (fun x : ℝ => psi x / x) atTop := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ : ℝ := min ε (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hcpos : (0 : ℝ) < 1 - δ := by linarith
  have hΔ : Tendsto (fun y : ℝ => (S y - S ((1 - δ) * y)) / y) atTop (𝓝 0) := by
    have h := S_diff_div_tendsto hS hcpos
    have := h.neg
    rw [neg_zero] at this
    refine this.congr ?_
    intro y
    ring
  have hg : Tendsto (fun y : ℝ => (1 - δ) * (1 + (S y - S ((1 - δ) * y)) / y / δ)) atTop
      (𝓝 (1 - δ)) := by
    have h1 : Tendsto (fun y : ℝ => 1 + (S y - S ((1 - δ) * y)) / y / δ) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (hΔ.div_const δ)
    simpa using h1.const_mul (1 - δ)
  have hev : ∀ᶠ y : ℝ in atTop,
      (1 - δ) * (1 + (S y - S ((1 - δ) * y)) / y / δ) ≤ psi y / y := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (4 / (1 - δ))] with y hy hy'
    have hy0 : (0 : ℝ) < y := by linarith
    have hlow : (2 : ℝ) ≤ (1 - δ) * y := by
      rw [div_le_iff₀ hcpos] at hy'
      nlinarith
    have hylt : (1 - δ) * y < y := by nlinarith
    have hmono : ∀ u : ℝ, u ∈ Set.Icc ((1 - δ) * y) y →
        R u / u ≤ psi y / ((1 - δ) * y) - 1 := by
      intro u hu
      have hu0 : (0 : ℝ) < u := by nlinarith [hu.1]
      have hden : (0 : ℝ) < (1 - δ) * y := by positivity
      have hle : psi u / u ≤ psi y / ((1 - δ) * y) := by
        rw [div_le_div_iff₀ hu0 hden]
        nlinarith [psi_mono hu.2, hu.1, psi_nonneg y, psi_nonneg u, hu0, hy0]
      have hR : R u / u = psi u / u - 1 := by
        simp only [R]
        field_simp
      rw [hR]
      linarith
    have hint := intervalIntegral.integral_mono_on hylt.le
      (intervalIntegrable_R_div (by positivity) hy0)
      (intervalIntegrable_const (c := psi y / ((1 - δ) * y) - 1)) hmono
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    rw [← S_sub_S hlow hy] at hint
    have hδy : (0 : ℝ) < δ * y := by positivity
    have hkey : (S y - S ((1 - δ) * y)) / (δ * y) ≤ psi y / ((1 - δ) * y) - 1 := by
      rw [div_le_iff₀ hδy]
      nlinarith [hint]
    have hexp : (S y - S ((1 - δ) * y)) / y / δ = (S y - S ((1 - δ) * y)) / (δ * y) := by
      field_simp
      try ring
    have hdiv : psi y / ((1 - δ) * y) = psi y / y / (1 - δ) := by
      field_simp
      try ring
    rw [hdiv] at hkey
    rw [hexp]
    have hcalc : psi y / y = (1 - δ) * (psi y / y / (1 - δ)) := by field_simp
    rw [hcalc]
    have := mul_le_mul_of_nonneg_left (show 1 + (S y - S ((1 - δ) * y)) / (δ * y) ≤
      psi y / y / (1 - δ) by linarith) hcpos.le
    linarith
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (fun x : ℝ => psi x / x) :=
    isCoboundedUnder_ge_of_le atTop psi_div_le_const
  have hle : (1 : ℝ) - δ ≤ liminf (fun x : ℝ => psi x / x) atTop := by
    calc (1 : ℝ) - δ = liminf (fun y : ℝ => (1 - δ) * (1 + (S y - S ((1 - δ) * y)) / y / δ)) atTop :=
          hg.liminf_eq.symm
      _ ≤ liminf (fun x : ℝ => psi x / x) atTop :=
          liminf_le_liminf hev hg.isBoundedUnder_ge hcob
  linarith

/-- `log x / √x → 0`. -/
theorem log_div_sqrt_tendsto : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
  rw [Real.sqrt_eq_rpow]

/-- From `ψ(x)/x → 1` to `θ(x)/x → 1`: the two differ by `O(√x log x)`
(`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`). -/
theorem theta_div_tendsto_one (hpsi : Tendsto (fun x : ℝ => psi x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  simp only [ElementaryPNT.psi_eq_chebyshevPsi] at hpsi
  have hdiff : Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    have hg : Tendsto (fun x : ℝ => 2 * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop (α := ℝ))).mul log_div_sqrt_tendsto
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x := h
      _ = 2 * (Real.log x / Real.sqrt x) * x := by
          field_simp
          rw [Real.sq_sqrt hx0.le]
          ring
  have hsub := hpsi.sub hdiff
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp
  ring

/-- From `θ(x)/x → 1` to `π(⌊x⌋)/(x/log x) → 1`, over a real variable
(`Chebyshev.primeCounting_sub_theta_div_log_isBigO`). -/
theorem primeCounting_div_tendsto_one
    (htheta : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  have hO := Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have hF : Tendsto (fun x : ℝ =>
      ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) * (Real.log x / x))
      atTop (𝓝 0) := by
    have h1 : (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) *
        (Real.log x / x)) =O[atTop] (fun x : ℝ => x / Real.log x ^ 2 * (Real.log x / x)) :=
      hO.mul (isBigO_refl _ _)
    refine h1.trans_tendsto ?_
    have heq : ∀ᶠ x : ℝ in atTop, 1 / Real.log x = x / Real.log x ^ 2 * (Real.log x / x) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
      have hx0 : x ≠ 0 := by positivity
      field_simp
    refine Tendsto.congr' heq ?_
    simpa using Real.tendsto_log_atTop.inv_tendsto_atTop
  have hsum := htheta.add hF
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hx0 : x ≠ 0 := by positivity
  field_simp
  ring

end Stage5Aux
end SelbergPNT
