/-
ElementaryPNT.Stage4b — Stage 4, the universal gap bound and `α ≤ κ`, and the endgame modulo the smoothing estimate.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage1b
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4bAux
import ElementaryPNT.Stage4bMertens
import ElementaryPNT.Stage4bGap
import ElementaryPNT.Stage5

open Filter Topology

namespace SelbergPNT

/-! ## S4.3: a universal bound for the integral of `|W|` over a gap -/

/-- (§"A universal bound for `∫₂^x S(y)/y² dy`", the two-way slicing). For `x ≥ 2`,
`∫₂^x S(y)/y² dy = ∫₂^x R(t)/t² dt − S(x)/x`.

Chapter proof: both sides are the volume under `R(t)/(y²t)` over the triangle `2 ≤ t ≤ y ≤ x`,
sliced the two ways. The inner integral `∫_t^x dy/y²` evaluates to `1/t − 1/x`. In Lean this is
`MeasureTheory.integral_integral_swap` on the triangle, or, avoiding Fubini, differentiation in
`x`: both sides vanish at `x = 2` and have derivative `S(x)/x²` almost everywhere, the right side
by the product rule together with `S'(x) = R(x)/x` at the points where `R` is continuous.
Either route is acceptable; 

The route used is the third one, differentiation in `x`, in a form that avoids "almost
everywhere" altogether: `ψ` is constant on a right neighbourhood of every point, so `R` is
right-continuous and `S` has the **right** derivative `R(x)/x` at every `x > 0`
(`Stage4bAux.hasDerivWithinAt_S`). Mathlib's `integral_eq_sub_of_hasDeriv_right_of_le` asks for
exactly a right derivative on the open interval, so no exceptional set has to be handled. -/
theorem integral_S_div_sq (x : ℝ) (hx : 2 ≤ x) :
    (∫ y in (2 : ℝ)..x, S y / y ^ 2) = (∫ t in (2 : ℝ)..x, R t / t ^ 2) - S x / x := by
  have hIcc : Set.Icc (2 : ℝ) x ⊆ Set.Ioi (0 : ℝ) := fun u hu =>
    lt_of_lt_of_le (by norm_num) hu.1
  set G : ℝ → ℝ := fun u => (∫ t in (2 : ℝ)..u, R t / t ^ 2) - S u / u with hGdef
  have hcont : ContinuousOn G (Set.Icc 2 x) := by
    refine (Stage4bAux.continuousOn_integral_R_div_sq.mono hIcc).sub ?_
    exact (Stage4bAux.continuousOn_S.mono hIcc).div continuousOn_id fun u hu => ne_of_gt (hIcc hu)
  have hderiv : ∀ y ∈ Set.Ioo (2 : ℝ) x, HasDerivWithinAt G (S y / y ^ 2) (Set.Ioi y) y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by linarith [hy.1]
    have h1 := Stage4bAux.hasDerivWithinAt_integral_R_div_sq hy0
    have h2 : HasDerivWithinAt (fun u : ℝ => S u / u) ((R y / y * y - S y * 1) / y ^ 2)
        (Set.Ioi y) y :=
      (Stage4bAux.hasDerivWithinAt_S hy0).div (hasDerivWithinAt_id y _) (ne_of_gt hy0)
    have h3 := h1.sub h2
    convert h3 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun y : ℝ => S y / y ^ 2) MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx]
    exact (Stage4bAux.continuousOn_S.mono hIcc).div (by fun_prop)
      fun u hu => pow_ne_zero 2 (ne_of_gt (hIcc hu))
  have hmain := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx hcont hderiv hint
  have hG2 : G 2 = 0 := by simp [hGdef, Stage4bAux.S_two]
  rw [hG2, sub_zero] at hmain
  exact hmain

/-- R13-2. The right side is bounded independently of `x`: `∫₂^x R(t)/t² dt = O(1)` by the
integral form of Mertens (`integral_psi_div_sq_isBigO`), since
`∫₂^x R(t)/t² dt = ∫₂^x ψ(t)/t² dt − (log x − log 2)` and the two `log x` cancel; and
`|S(x)/x| ≤ 1` by stage 12. Hence a universal bound for `∫₂^x S(y)/y² dy`.

Round 12's `integral_psi_div_sq_isBigO` is not quite enough for this, since it only gives
`∫₂^x ψ(t)/t² dt = O(log x)`, with no control of the constant in front of `log x`; the exact
cancellation needs the partial-summation identity
`∫₂^x ψ(t)/t² dt = ∑_{n ≤ x} Λ(n)/n − ψ(x)/x`, which is proved in
`ElementaryPNT/Stage4bMertens.lean` and combined there with the Mertens. -/
theorem integral_S_div_sq_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → |∫ y in (2 : ℝ)..x, S y / y ^ 2| ≤ C := by
  obtain ⟨C, hC, hbd⟩ := Stage4bMertens.abs_integral_R_div_sq_le
  refine ⟨C + 1, by linarith, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 := hbd x hx
  have h2 : |S x / x| ≤ 1 := by
    rw [abs_div, abs_of_pos hx0, div_le_one hx0]
    have := abs_S_le x hx
    linarith
  rw [integral_S_div_sq x hx]
  calc |(∫ t in (2 : ℝ)..x, R t / t ^ 2) - S x / x|
      ≤ |∫ t in (2 : ℝ)..x, R t / t ^ 2| + |S x / x| := abs_sub _ _
    _ ≤ C + 1 := by linarith

/-- (chapter step S4.3). A bound for
`∫ Wtr` over any interval in `[0,∞)` on which `Wtr` does not vanish, uniform in the interval.

Chapter proof: on such an interval the continuous `W` has constant sign, so `∫_a^b |W| = |∫_a^b W|`;
the substitution `y = e^v` turns this into `|∫_{e^a}^{e^b} S(y)/y² dy|`, which bounds by
`2C` after splitting at `2`, plus `∫₁²(2−y)/y² dy = 1 − log 2 < 1` for the part below `2`, where
`S(y) = 2 − y`. The hypothesis `0 ≤ a` is needed: without it the blow-up of `W` at `−∞` makes the
claim false (an earlier review §2.7, §2.10). -/
theorem Wtr_integral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → Wtr v ≠ 0) →
      (∫ v in a..b, Wtr v) ≤ K := by
  obtain ⟨C, hC, hbd⟩ := integral_S_div_sq_bounded
  refine ⟨2 * C + 1, by linarith, fun a b ha hab hne => ?_⟩
  have hWne : ∀ v : ℝ, a < v → v < b → W v ≠ 0 := by
    intro v h1 h2
    have hv0 : (0 : ℝ) ≤ v := le_trans ha h1.le
    have h := hne v h1 h2
    rw [Wtr_agrees.1 v hv0] at h
    exact fun hW => h (by rw [hW, abs_zero])
  have hcongr : (∫ v in a..b, Wtr v) = ∫ v in a..b, |W v| := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hab.le] at hv
    exact Wtr_agrees.1 v (le_trans ha hv.1)
  rw [hcongr, Stage4bGap.integral_abs_W_eq_abs_integral hab hWne, Stage4bGap.integral_W_eq]
  exact Stage4bGap.abs_integral_S_div_sq_le_of_bound hbd (Real.one_le_exp ha)
    (Real.exp_le_exp.2 hab.le)

/-! ## S5.1: essential bounds for averages give essential bounds for values -/

/-- (§"Essential bounds for averages give essential bounds for values", the slicing).
For `x > 0`, `∫₀^x |W(v)|(x − v) dv = ∫₀^x (∫₀^u |W(v)| dv) du`.

Chapter proof: both sides are the volume under the `|W|`-surface over the triangle
`0 ≤ v ≤ u ≤ x`, sliced the two ways. As in R13-1, either Fubini or differentiation in `x` will
do; the latter needs only that `u ↦ ∫₀^u |W|` is continuous.

The route used is the second one, in the form of an integration by parts: `u ↦ ∫₀^u Wtr` is
differentiable with derivative `Wtr`, `Wtr` being continuous, so
`∫₀^x (∫₀^u Wtr) du = x∫₀^x Wtr − ∫₀^x v·Wtr(v) dv`, which is the left-hand side expanded
(`Stage4bAux.integral_Wtr_mul_sub`). -/
theorem integral_mul_sub_eq_integral_integral (x : ℝ) (hx : 0 < x) :
    (∫ v in (0 : ℝ)..x, |W v| * (x - v)) = ∫ u in (0 : ℝ)..x, ∫ v in (0 : ℝ)..u, |W v| := by
  have h1 : (∫ v in (0 : ℝ)..x, |W v| * (x - v)) = ∫ v in (0 : ℝ)..x, Wtr v * (x - v) := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hx.le] at hv
    simp only [← Wtr_agrees.1 v hv.1]
  have h2 : (∫ u in (0 : ℝ)..x, ∫ v in (0 : ℝ)..u, |W v|)
      = ∫ u in (0 : ℝ)..x, ∫ v in (0 : ℝ)..u, Wtr v := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le hx.le] at hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · simp [← h]
    · exact (Wtr_agrees.2.1 u h).symm
  rw [h1, h2]
  exact Stage4bAux.integral_Wtr_mul_sub x

/-- (chapter step S5.1). `α ≤ κ` for the truncation:
`limsup Wtr ≤ limsup (1/x)∫₀^x Wtr`.

This is where Selberg's inequality is finally consumed, through the hypothesis `hsmooth`, which
is S4.1 (the next stage's target) stated for `Wtr`; `Wtr v = |W v|` for `v ≥ 0` makes the two
readings the same on the range that matters.

Chapter proof: write `κ` for the right-hand `limsup`, fix `ε > 0`, and let `t` be a point beyond
which `(1/u)∫₀^u Wtr ≤ κ + ε`. By R13-4,
`(2/x²)∫₀^x Wtr(v)(x − v) dv = (2/x²)∫₀^x u·((1/u)∫₀^u Wtr) du`, and since `(2/x²)∫₀^x u du = 1`
this is a weighted average of those averages. Splitting at `t`,
`≤ (2/x²)∫₀^t (∫₀^u Wtr) du + (κ + ε)`, and the first term is `K₅/x²` with `K₅` independent of
`x`. With `hsmooth` this gives `Wtr x ≤ κ + ε + K₅/x² + K/x` for large `x`, hence
`limsup Wtr ≤ κ + ε` for every `ε`. -/
theorem alpha_le_kappa_tr
    (hsmooth : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      Wtr x ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) + K / x) :
    limsup (fun x : ℝ => Wtr x) atTop ≤
      limsup (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, Wtr v) atTop := by
  obtain ⟨K, hK, hev⟩ := hsmooth
  set avg : ℝ → ℝ := fun x => (1 / x) * ∫ v in (0 : ℝ)..x, Wtr v with havgdef
  set κ : ℝ := limsup avg atTop with hκdef
  have havg_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ avg x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (by positivity) (Stage4bAux.integral_Wtr_nonneg hx.le)
  have havg_le : ∀ᶠ x : ℝ in atTop, avg x ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := Stage4bAux.integral_Wtr_le hx.le
    have h2 : (1 / x) * (∫ v in (0 : ℝ)..x, Wtr v) ≤ (1 / x) * x :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (1 / x) * x = 1 := by field_simp
    show (1 / x) * (∫ v in (0 : ℝ)..x, Wtr v) ≤ 1
    linarith
  have hbdd : IsBoundedUnder (· ≤ ·) atTop avg := isBoundedUnder_of_eventually_le havg_le
  have hκ0 : 0 ≤ κ := le_limsup_of_frequently_le havg_nonneg.frequently hbdd
  have hWcob : IsCoboundedUnder (· ≤ ·) atTop (fun x : ℝ => Wtr x) :=
    isCoboundedUnder_le_of_eventually_le atTop (x := 0)
      (Eventually.of_forall fun x => Wtr_properties.1 x)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a point `T` beyond which the running averages are below `κ + ε/2`
  have h1 : ∀ᶠ x : ℝ in atTop, avg x ≤ κ + ε / 2 := by
    filter_upwards [eventually_lt_of_limsup_lt (show κ < κ + ε / 2 by linarith) hbdd] with x hx
    exact hx.le
  obtain ⟨t, ht⟩ := eventually_atTop.1 h1
  set T : ℝ := max t 1 with hT
  have hT1 : (1 : ℝ) ≤ T := le_max_right t 1
  have hT0 : (0 : ℝ) < T := by linarith
  set K₅ : ℝ := ∫ u in (0 : ℝ)..T, ∫ v in (0 : ℝ)..u, Wtr v with hK5
  have hK5nn : 0 ≤ K₅ :=
    intervalIntegral.integral_nonneg hT0.le fun u hu => Stage4bAux.integral_Wtr_nonneg hu.1
  -- the weighted average of the running averages, split at `T`
  have hmain : ∀ x : ℝ, T ≤ x →
      (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) ≤ κ + ε / 2 + 2 * K₅ / x ^ 2 := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hT0 hx
    rw [Stage4bAux.integral_Wtr_mul_sub x]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (f := fun u : ℝ => ∫ v in (0 : ℝ)..u, Wtr v) (a := (0 : ℝ)) (b := T) (c := x)
      (μ := MeasureTheory.volume)
      (Stage4bAux.continuous_integral_Wtr.intervalIntegrable 0 T)
      (Stage4bAux.continuous_integral_Wtr.intervalIntegrable T x)
    have hmono : (∫ u in T..x, ∫ v in (0 : ℝ)..u, Wtr v) ≤ ∫ u in T..x, (κ + ε / 2) * u := by
      refine intervalIntegral.integral_mono_on hx
        (Stage4bAux.continuous_integral_Wtr.intervalIntegrable T x)
        ((continuous_const.mul continuous_id).intervalIntegrable T x) fun u hu => ?_
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hT0 hu.1
      have havgu : (1 / u) * (∫ v in (0 : ℝ)..u, Wtr v) ≤ κ + ε / 2 :=
        ht u (le_trans (le_max_left t 1) hu.1)
      calc (∫ v in (0 : ℝ)..u, Wtr v) = u * ((1 / u) * ∫ v in (0 : ℝ)..u, Wtr v) := by
            field_simp
        _ ≤ u * (κ + ε / 2) := mul_le_mul_of_nonneg_left havgu hu0.le
        _ = (κ + ε / 2) * u := by ring
    have hval : (∫ u in T..x, (κ + ε / 2) * u) = (κ + ε / 2) * ((x ^ 2 - T ^ 2) / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
    have hle : (∫ u in T..x, ∫ v in (0 : ℝ)..u, Wtr v) ≤ (κ + ε / 2) * (x ^ 2 / 2) := by
      rw [hval] at hmono
      nlinarith [hmono, sq_nonneg T, hκ0, hε.le]
    have h2x : (0 : ℝ) < 2 / x ^ 2 := by positivity
    have hstep : (2 / x ^ 2) * (∫ u in T..x, ∫ v in (0 : ℝ)..u, Wtr v) ≤ κ + ε / 2 :=
      calc (2 / x ^ 2) * (∫ u in T..x, ∫ v in (0 : ℝ)..u, Wtr v)
          ≤ (2 / x ^ 2) * ((κ + ε / 2) * (x ^ 2 / 2)) := mul_le_mul_of_nonneg_left hle h2x.le
        _ = κ + ε / 2 := by field_simp
    have hK5eq : (2 / x ^ 2) * K₅ = 2 * K₅ / x ^ 2 := by ring
    rw [← hsplit, ← hK5, mul_add]
    linarith
  -- the two error terms tend to zero
  have htend : Tendsto (fun x : ℝ => 2 * K₅ / x ^ 2 + K / x) atTop (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => 2 * K₅ / x ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    have hb : Tendsto (fun x : ℝ => K / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using ha.add hb
  have herr : ∀ᶠ x : ℝ in atTop, 2 * K₅ / x ^ 2 + K / x ≤ ε / 2 :=
    htend.eventually_le_const (by linarith)
  refine limsup_le_of_le hWcob ?_
  filter_upwards [hev, eventually_ge_atTop T, herr] with x hx1 hx2 hx3
  have h4 := hmain x hx2
  linarith

/-- The shape of `hsmooth` is exactly what the S4.1 chain will deliver : the
blueprint's `W_le_average` is the same statement with `|W|` in place of `Wtr`, and since
`Wtr v = |W v|` for `v ≥ 0` — which is all that the eventual quantifier and the range of
integration see — the one implies the other with no further glue. This is not a proof of S4.1;
it is the transfer that makes discharging `hsmooth` in a later stage a single step. -/
theorem smoothing_tr_of_smoothing_abs
    (h : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      |W x| ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, |W v| * (x - v)) + K / x) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      Wtr x ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) + K / x := by
  obtain ⟨K, hK, hev⟩ := h
  refine ⟨K, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with x h1 h2
  have hI : (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) = ∫ v in (0 : ℝ)..x, |W v| * (x - v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le h2] at hv
    simp only [Wtr_agrees.1 v hv.1]
  rw [Wtr_agrees.1 x h2, hI]
  exact h1

/-! ## The endgame, modulo S4.1 -/

/-- R13-6. `W → 0`, given the smoothing estimate. Proof: supplies the first three
hypotheses of for `Wtr` with `B = 1`, `L = 2`; supplies `havg`; supplies
`hint`. then gives `Tendsto Wtr atTop (𝓝 0)`, and the first conjunct of transfers it
to `|W|`, hence to `W`. -/
theorem W_tendsto_zero_of_smoothing
    (hsmooth : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      Wtr x ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) + K / x) :
    Tendsto W atTop (𝓝 0) := by
  obtain ⟨K, hK, hint⟩ := Wtr_integral_bound
  obtain ⟨L, hL, hlip⟩ := Wtr_properties.2.2
  have h : Tendsto Wtr atTop (𝓝 0) :=
    tendsto_zero_of_three_conditions (f := Wtr) (L := L) (K := K) (B := 1)
      Wtr_properties.1 Wtr_properties.2.1 hlip (alpha_le_kappa_tr hsmooth) hint
  have habs : Tendsto (fun x : ℝ => |W x|) atTop (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx using Wtr_agrees.1 x hx
  exact (tendsto_zero_iff_abs_tendsto_zero W).2 habs

/-- R13-7. `S(x)/x → 0`, given the same hypothesis. Proof: `S(x)/x = W(log x)` for `x > 0`, and
`log x → ∞`. -/
theorem S_div_tendsto_zero_of_smoothing
    (hsmooth : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      Wtr x ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) + K / x) :
    Tendsto (fun x : ℝ => S x / x) atTop (𝓝 0) := by
  have h := (W_tendsto_zero_of_smoothing hsmooth).comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, W, Real.exp_log hx]

/-- R13-8. **The prime number theorem, modulo the smoothing estimate.** Round 11's bridges
(`psi_asymptotic_of_S`, `primeCounting_asymptotic_of_psi`) applied to R13-7. After the S4.1 chain
is proved, discharging `hsmooth` turns this into the unconditional statement. -/
theorem primeCounting_asymptotic_of_smoothing
    (hsmooth : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      Wtr x ≤ (2 / x ^ 2) * (∫ v in (0 : ℝ)..x, Wtr v * (x - v)) + K / x) :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) :=
  primeCounting_asymptotic_of_psi (psi_asymptotic_of_S (S_div_tendsto_zero_of_smoothing hsmooth))

end SelbergPNT
