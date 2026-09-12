/-
ElementaryPNT.Stage4bAux — auxiliary development for `ElementaryPNT.Stage4b`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage1b
import ElementaryPNT.Stage4a

open Filter Topology MeasureTheory

namespace SelbergPNT
namespace Stage4bAux

/-! ## Right-continuity of `ψ` -/

/-- `ψ` is constant on a right neighbourhood of every point: `⌊·⌋₊` is. -/
theorem psi_eventuallyEq_right (x : ℝ) : ∀ᶠ y in 𝓝[≥] x, psi y = psi x := by
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  filter_upwards [Ico_mem_nhdsGE hlt] with y hy
  have h1 : ⌊y⌋₊ = ⌊x⌋₊ := by
    have h2 : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hy.1
    have h3 : ⌊y⌋₊ ≤ ⌊x⌋₊ :=
      Nat.le_of_lt_succ (Nat.floor_lt' (by omega) |>.2 (by push_cast; exact hy.2))
    omega
  simp [psi, h1]

theorem measurable_R_div : Measurable (fun u : ℝ => R u / u) :=
  (Stage5Aux.psi_mono.measurable.sub measurable_id).div measurable_id

theorem measurable_R_div_sq : Measurable (fun u : ℝ => R u / u ^ 2) :=
  (Stage5Aux.psi_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)

/-- `u ↦ R u / u` is right-continuous away from the origin. -/
theorem continuousWithinAt_R_div {x : ℝ} (hx : 0 < x) :
    ContinuousWithinAt (fun u : ℝ => R u / u) (Set.Ioi x) x := by
  have h : ∀ᶠ y in 𝓝[>] x, (fun u : ℝ => R u / u) y = (fun u : ℝ => (psi x - u) / u) y := by
    filter_upwards [nhdsWithin_mono x Set.Ioi_subset_Ici_self (psi_eventuallyEq_right x)] with y hy
    simp [R, hy]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ h ?_
  · exact ContinuousWithinAt.div (by fun_prop) continuousWithinAt_id (ne_of_gt hx)
  · simp [R]

/-- `u ↦ R u / u²` is right-continuous away from the origin. -/
theorem continuousWithinAt_R_div_sq {x : ℝ} (hx : 0 < x) :
    ContinuousWithinAt (fun u : ℝ => R u / u ^ 2) (Set.Ioi x) x := by
  have h : ∀ᶠ y in 𝓝[>] x, (fun u : ℝ => R u / u ^ 2) y = (fun u : ℝ => (psi x - u) / u ^ 2) y := by
    filter_upwards [nhdsWithin_mono x Set.Ioi_subset_Ici_self (psi_eventuallyEq_right x)] with y hy
    simp [R, hy]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ h ?_
  · exact ContinuousWithinAt.div (by fun_prop) (by fun_prop) (by positivity)
  · simp [R]

/-- `u ↦ R u / u²` is interval integrable away from the origin: `ψ` is monotone, hence
measurable, and `|R u / u²| ≤ 2/u` there. -/
theorem intervalIntegrable_R_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => R u / u ^ 2) volume a b := by
  have hpos : ∀ u : ℝ, u ∈ Set.uIcc a b → u ≠ 0 := by
    intro u hu
    refine ne_of_gt (lt_of_lt_of_le (lt_min ha hb) ?_)
    rw [Set.uIcc_eq_union] at hu
    rcases hu with hu | hu
    · exact le_trans (min_le_left a b) hu.1
    · exact le_trans (min_le_right a b) hu.1
  have h1 : IntervalIntegrable psi volume a b :=
    (Stage5Aux.psi_mono.monotoneOn (Set.uIcc a b)).intervalIntegrable
  have h2 : IntervalIntegrable (fun u : ℝ => psi u * (1 / u ^ 2)) volume a b :=
    h1.mul_continuousOn (ContinuousOn.div continuousOn_const (by fun_prop)
      (fun u hu => pow_ne_zero 2 (hpos u hu)))
  have h3 : IntervalIntegrable (fun u : ℝ => 1 / u) volume a b :=
    (ContinuousOn.div continuousOn_const continuousOn_id hpos).intervalIntegrable
  refine IntervalIntegrable.congr (f := fun u : ℝ => psi u * (1 / u ^ 2) - 1 / u) ?_ (h2.sub h3)
  intro u hu
  have hu0 : u ≠ 0 := hpos u (Set.uIoc_subset_uIcc hu)
  simp only [R]
  field_simp

/-! ## The fundamental theorem of calculus, in its right-derivative form -/

/-- `S` has the right derivative `R x / x` at every `x > 0`. -/
theorem hasDerivWithinAt_S {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt S (R x / x) (Set.Ioi x) x := by
  have hmeas : StronglyMeasurableAtFilter (fun u : ℝ => R u / u) (𝓝[>] x) :=
    ⟨Set.univ, univ_mem, measurable_R_div.aestronglyMeasurable⟩
  have h := intervalIntegral.integral_hasDerivWithinAt_right
    (f := fun u : ℝ => R u / u) (a := (2 : ℝ)) (b := x) (s := Set.Ici x) (t := Set.Ioi x)
    (Stage5Aux.intervalIntegrable_R_div (by norm_num) hx) hmeas (continuousWithinAt_R_div hx)
  exact h.mono Set.Ioi_subset_Ici_self

/-- The same for the primitive of `R u / u²`. -/
theorem hasDerivWithinAt_integral_R_div_sq {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (fun u : ℝ => ∫ t in (2 : ℝ)..u, R t / t ^ 2) (R x / x ^ 2) (Set.Ioi x) x := by
  have hmeas : StronglyMeasurableAtFilter (fun u : ℝ => R u / u ^ 2) (𝓝[>] x) :=
    ⟨Set.univ, univ_mem, measurable_R_div_sq.aestronglyMeasurable⟩
  have h := intervalIntegral.integral_hasDerivWithinAt_right
    (f := fun u : ℝ => R u / u ^ 2) (a := (2 : ℝ)) (b := x) (s := Set.Ici x) (t := Set.Ioi x)
    (intervalIntegrable_R_div_sq (by norm_num) hx) hmeas (continuousWithinAt_R_div_sq hx)
  exact h.mono Set.Ioi_subset_Ici_self

/-! ## Continuity -/

/-- `S` is continuous away from the origin, being `1`-Lipschitz there
(`Stage4aAux.abs_S_sub_le`). -/
theorem continuousOn_S : ContinuousOn S (Set.Ioi 0) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) ?_).continuousOn
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  exact Stage4aAux.abs_S_sub_le hy hx

/-- The primitive of `R u / u²` is continuous away from the origin. -/
theorem continuousOn_integral_R_div_sq :
    ContinuousOn (fun u : ℝ => ∫ t in (2 : ℝ)..u, R t / t ^ 2) (Set.Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  set b₁ : ℝ := min (x / 2) 1 with hb1
  set b₂ : ℝ := max (x + 1) 3 with hb2
  have hb1pos : 0 < b₁ := lt_min (by linarith) one_pos
  have hb1x : b₁ < x := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hxb2 : x < b₂ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hble : b₁ ≤ b₂ := by
    linarith [le_max_right (x + 1) (3 : ℝ), min_le_right (x / 2) (1 : ℝ)]
  have h2mem : (2 : ℝ) ∈ Set.uIcc b₁ b₂ := by
    rw [Set.uIcc_of_le hble]
    exact ⟨by linarith [min_le_right (x / 2) (1 : ℝ)], by linarith [le_max_right (x + 1) (3 : ℝ)]⟩
  have hcont := intervalIntegral.continuousOn_primitive_interval'
    (f := fun t : ℝ => R t / t ^ 2) (μ := volume) (a := (2 : ℝ)) (b₁ := b₁) (b₂ := b₂)
    (intervalIntegrable_R_div_sq hb1pos (by linarith)) h2mem
  have hmem : Set.uIcc b₁ b₂ ∈ 𝓝 x := by
    rw [Set.uIcc_of_le hble]
    exact Icc_mem_nhds hb1x hxb2
  exact ((hcont x (mem_of_mem_nhds hmem)).continuousAt hmem).continuousWithinAt

/-- `W` is continuous: `W u = S(eᵘ)/eᵘ` and `S` is continuous on `(0,∞)`. -/
theorem continuous_W : Continuous W :=
  (ContinuousOn.comp_continuous continuousOn_S Real.continuous_exp
    fun u => Real.exp_pos u).div Real.continuous_exp fun u => (Real.exp_pos u).ne'

/-- `Wtr` is continuous: it is `|W| ∘ (max · 0)`. -/
theorem continuous_Wtr : Continuous Wtr :=
  (continuous_W.comp (continuous_id.max continuous_const)).abs

theorem intervalIntegrable_Wtr (a b : ℝ) : IntervalIntegrable Wtr volume a b :=
  continuous_Wtr.intervalIntegrable a b

/-- `S 2 = 0`. -/
theorem S_two : S 2 = 0 := by simp [S]

/-! ## The running integral of `Wtr` -/

theorem integral_Wtr_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ ∫ v in (0 : ℝ)..x, Wtr v :=
  intervalIntegral.integral_nonneg hx fun v _ => Wtr_properties.1 v

theorem integral_Wtr_le {x : ℝ} (hx : 0 ≤ x) : (∫ v in (0 : ℝ)..x, Wtr v) ≤ x := by
  have h : (∫ v in (0 : ℝ)..x, Wtr v) ≤ ∫ _v in (0 : ℝ)..x, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hx (continuous_Wtr.intervalIntegrable 0 x)
      intervalIntegrable_const fun v _ => Wtr_properties.2.1 v
  simpa using h

/-- The inner integral `u ↦ ∫₀^u Wtr` has derivative `Wtr u` everywhere, `Wtr` being
continuous. -/
theorem hasDerivAt_integral_Wtr (u : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ v in (0 : ℝ)..t, Wtr v) (Wtr u) u :=
  (continuous_Wtr.integral_hasStrictDerivAt 0 u).hasDerivAt

theorem continuous_integral_Wtr : Continuous (fun u : ℝ => ∫ v in (0 : ℝ)..u, Wtr v) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_integral_Wtr u).continuousAt

/-- The two-way slicing of R13-4, for `Wtr`: an integration by parts, since `u ↦ ∫₀^u Wtr` is
differentiable with derivative `Wtr`. -/
theorem integral_Wtr_mul_sub (x : ℝ) :
    (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) = ∫ u in (0 : ℝ)..x, ∫ v in (0 : ℝ)..u, Wtr v := by
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ : ℝ => (1 : ℝ))
    (v := fun t : ℝ => ∫ v in (0 : ℝ)..t, Wtr v) (v' := Wtr) (a := (0 : ℝ)) (b := x)
    (fun t _ => hasDerivAt_id t) (fun t _ => hasDerivAt_integral_Wtr t)
    intervalIntegrable_const (continuous_Wtr.intervalIntegrable 0 x)
  simp only [one_mul, zero_mul, sub_zero] at hIBP
  have hint1 : IntervalIntegrable (fun v : ℝ => x * Wtr v) volume 0 x :=
    (continuous_Wtr.intervalIntegrable 0 x).const_mul x
  have hint2 : IntervalIntegrable (fun v : ℝ => v * Wtr v) volume 0 x :=
    (continuous_id'.mul continuous_Wtr).intervalIntegrable 0 x
  have hsplit : (∫ v in (0 : ℝ)..x, Wtr v * (x - v))
      = (∫ v in (0 : ℝ)..x, x * Wtr v) - ∫ v in (0 : ℝ)..x, v * Wtr v := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    exact intervalIntegral.integral_congr fun v _ => by ring
  rw [hsplit, intervalIntegral.integral_const_mul, hIBP]
  ring

end Stage4bAux
end SelbergPNT
