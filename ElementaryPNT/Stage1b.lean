/-
ElementaryPNT.Stage1b — Stage 1b: the three-condition criterion for a function to tend to zero.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1bAux
import ElementaryPNT.Stage1bWalk

open Filter Topology

namespace SelbergPNT

/-! ## One gap -/

/-- (chapter step S1.2a). On a gap `[a,b]` where `W` vanishes at `a`, is nonnegative, bounded
by `B`, and has all chords of slope at most `K`, the graph lies under both `K(x−a)` and `B`, so
`∫_a^b W ≤ ∫_a^b min (K(x−a)) B`. A closed form for this bound is not available: `min (Kℓ²/2) (Bℓ − B²/(2K))` fails for `W ≡ 0`.

Chapter proof: `W x = |W x − W a| ≤ K(x−a)` by the chord condition, and `W x ≤ B`; integrate. -/
theorem gap_integral_le_min {W : ℝ → ℝ} {a b B K : ℝ} (hab : a ≤ b) (hK : 0 < K) (hB : 0 < B)
    (hnonneg : ∀ x : ℝ, 0 ≤ W x) (hzero : W a = 0) (hbdd : ∀ x : ℝ, W x ≤ B)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) :
    (∫ x in a..b, W x) ≤ ∫ x in a..b, min (K * (x - a)) B :=
  Stage1bAux.integral_le_integral_min hab hK.le hzero (fun v _ => hbdd v) hchord

/-- (chapter step S1.2a). The elementary evaluation of that comparison integral:
`K ℓ²/2` if `ℓ ≤ B/K`, and `Bℓ − B²/(2K)` otherwise (the triangle and the trapezoid of the
chapter). -/
theorem integral_min_ramp {a b B K : ℝ} (hab : a ≤ b) (hK : 0 < K) (hB : 0 < B) :
    (∫ x in a..b, min (K * (x - a)) B) =
      if b - a ≤ B / K then K * (b - a) ^ 2 / 2 else B * (b - a) - B ^ 2 / (2 * K) :=
  Stage1bAux.integral_min_ramp_eval hab hK hB

/-- (chapter step S1.2b). The crossover. With `B² ≤ 2MK`, the average of `W` over a gap whose
integral is at most `M` never exceeds `2MBK/(B² + 2MK)`, whatever the gap length.

Chapter proof (§"Some special conditions that depress the average of a function"): the triangular
bound `Kℓ/2` increases in `ℓ`, the trapezoidal-or-gap bound `min (B − B²/(2Kℓ)) (M/ℓ)` decreases
in `ℓ`, and they cross at `ℓ = B/(2K) + M/B`, where both equal `2MBK/(B² + 2MK)`. The hypothesis
`B² ≤ 2MK` is what places the crossover in the trapezoidal regime; an earlier review shows
the claim false without it (a truncated ramp). -/
theorem gap_average_le {W : ℝ → ℝ} {a b B K M : ℝ} (hab : a < b) (hK : 0 < K) (hB : 0 < B)
    (hM : 0 < M) (hBM : B ^ 2 ≤ 2 * M * K)
    (hnonneg : ∀ x : ℝ, 0 ≤ W x) (hzero : W a = 0) (hbdd : ∀ x : ℝ, W x ≤ B)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) (hgap : (∫ x in a..b, W x) ≤ M) :
    (∫ x in a..b, W x) / (b - a) ≤ 2 * M * B * K / (B ^ 2 + 2 * M * K) := by
  have hmul := Stage1bAux.gap_integral_le_mul hab hK hB hM hBM hzero (fun v _ => hbdd v) hchord hgap
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < b - a)]
  linarith

/-! ## From one gap to `[0,x]`, without components -/

/-- The `limsup` bookkeeping: an eventual bound `∫_0^x W ≤ c x + D` on the running integral gives
`limsup` of the running averages at most `c`. -/
private theorem limsup_average_le {W : ℝ → ℝ} {c D : ℝ} (hnonneg : ∀ x : ℝ, 0 ≤ W x)
    (h : ∀ᶠ x : ℝ in atTop, (∫ v in (0 : ℝ)..x, W v) ≤ c * x + D) :
    limsup (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, W v) atTop ≤ c := by
  have hev : ∀ᶠ x : ℝ in atTop, (1 / x) * (∫ v in (0 : ℝ)..x, W v) ≤ c + D / x := by
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hx0]
    have hxx : D / x * x = D := by field_simp
    nlinarith [hx]
  have hlim : Tendsto (fun x : ℝ => c + D / x) atTop (𝓝 c) := by
    have hD : Tendsto (fun x : ℝ => D / x) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    simpa using tendsto_const_nhds.add hD
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, W v) := by
    refine isCoboundedUnder_le_of_eventually_le atTop (x := 0) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hx.le fun v _ => hnonneg v)
  calc limsup (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, W v) atTop
      ≤ limsup (fun x : ℝ => c + D / x) atTop :=
        limsup_le_limsup hev hcob hlim.isBoundedUnder_le
    _ = c := hlim.limsup_eq

/-- The tail form of R11-4: the running integral from a point `T` beyond which `W` is bounded by
`B`. This is what consumes, and is its case `T = 0`. -/
private theorem tail_integral_le {W : ℝ → ℝ} {T B K M : ℝ} (hT : 0 ≤ T) (hK : 0 < K) (hB : 0 < B)
    (hM : 0 < M) (hBM : B ^ 2 ≤ 2 * M * K) (hbdd : ∀ x : ℝ, T ≤ x → W x ≤ B)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|)
    (hgap : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ M) :
    ∀ x : ℝ, T ≤ x →
      (∫ v in T..x, W v) ≤ 2 * M * B * K / (B ^ 2 + 2 * M * K) * (x - T) + M := by
  have hden : 0 < B ^ 2 + 2 * M * K := by positivity
  refine Stage1bAux.walk_bound hK hM.le (by positivity) hchord ?_ ?_
  · intro a b ha hab hne
    exact hgap a b (le_trans hT ha) hab hne
  · intro a b ha hab hzero hne
    exact Stage1bAux.gap_integral_le_mul hab hK hB hM hBM hzero
      (fun v hv => hbdd v (le_trans ha hv.1)) hchord (hgap a b (le_trans hT ha) hab hne)

/-- The unconditional tail bound, with no `B`: the second regime of the endgame of R11-6. -/
private theorem tail_integral_le_sqrt {W : ℝ → ℝ} {K M : ℝ} (hK : 0 < K) (hM : 0 < M)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|)
    (hgap : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ M) :
    ∀ x : ℝ, 0 ≤ x → (∫ v in (0 : ℝ)..x, W v) ≤ Real.sqrt (M * K / 2) * x + M := by
  intro x hx
  have := Stage1bAux.walk_bound (T := 0) hK hM.le (Real.sqrt_nonneg _) hchord
    (fun a b ha hab hne => hgap a b ha hab hne)
    (fun a b ha hab hzero hne =>
      Stage1bAux.gap_integral_le_sqrt hab hK hM hzero hchord (hgap a b ha hab hne)) x hx
  simpa using this

/-- (chapter step S1.2c). The running average obeys the same bound, with error `2M/x`.

This avoids the decomposition of `{v : W v ≠ 0}` into connected components. The route used:
define `z(v)` to be the last zero of
`W` at or before `v` (the supremum of `{u ≤ v : W u = 0}`, which is attained because `W` is
continuous), and induct along the finitely many steps `0 = v₀ < v₁ < ⋯` obtained by walking from
each zero to the next zero past it. 

If `W` has no zero in `[0,x]` at all, `hgap` bounds the whole integral by `M`, and the claim is
the `2M/x` term alone. -/
theorem average_le_of_gaps {W : ℝ → ℝ} {B K M : ℝ} (hK : 0 < K) (hB : 0 < B) (hM : 0 < M)
    (hBM : B ^ 2 ≤ 2 * M * K)
    (hcont : Continuous W)
    (hnonneg : ∀ x : ℝ, 0 ≤ W x) (hbdd : ∀ x : ℝ, W x ≤ B)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|)
    (hgap : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ M) :
    ∀ x : ℝ, 0 < x →
      (1 / x) * (∫ v in (0 : ℝ)..x, W v) ≤ 2 * M * B * K / (B ^ 2 + 2 * M * K) + 2 * M / x := by
  intro x hx
  have h := tail_integral_le (T := 0) le_rfl hK hB hM hBM (fun v _ => hbdd v) hchord
    hgap x hx.le
  rw [sub_zero] at h
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hx]
  have hxx : 2 * M / x * x = 2 * M := by field_simp
  nlinarith [h, hM.le]

/-- (chapter step S1.2d). Essential boundedness, in the `∀ ε, ∀ᶠ x` form an earlier review
recommends both for the hypothesis and as the workhorse. -/
theorem average_le_of_gaps_essential {W : ℝ → ℝ} {B K M : ℝ} (hK : 0 < K) (hB : 0 < B)
    (hM : 0 < M) (hcont : Continuous W) (hnonneg : ∀ x : ℝ, 0 ≤ W x)
    (hess : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, W x ≤ B + ε)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|)
    (hgap : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ M) :
    ∀ ε : ℝ, 0 < ε → (B + ε) ^ 2 ≤ 2 * M * K →
      limsup (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, W v) atTop ≤
        2 * M * (B + ε) * K / ((B + ε) ^ 2 + 2 * M * K) := by
  intro ε hε hBM
  obtain ⟨T₀, hT₀⟩ := (hess ε hε).exists_forall_of_atTop
  set T : ℝ := max T₀ 0 with hTdef
  have hT : 0 ≤ T := le_max_right _ _
  have hbddT : ∀ x : ℝ, T ≤ x → W x ≤ B + ε := fun x hx =>
    hT₀ x (le_trans (le_max_left _ _) hx)
  set c : ℝ := 2 * M * (B + ε) * K / ((B + ε) ^ 2 + 2 * M * K) with hcdef
  have hBε : 0 < B + ε := by linarith
  have hc0 : 0 ≤ c := by positivity
  have htail := tail_integral_le hT hK hBε hM hBM hbddT hchord hgap
  set C : ℝ := ∫ v in (0 : ℝ)..T, W v with hCdef
  refine limsup_average_le (D := C + M) hnonneg ?_
  filter_upwards [eventually_ge_atTop T] with x hxT
  have hsplit : (∫ v in (0 : ℝ)..x, W v) = C + ∫ v in T..x, W v := by
    rw [hCdef]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((Stage1bAux.continuous_of_chord hK.le hchord).intervalIntegrable 0 T)
      ((Stage1bAux.continuous_of_chord hK.le hchord).intervalIntegrable T x)).symm
  have hb := htail x hxT
  have hcx : c * (x - T) ≤ c * x := by nlinarith
  linarith [hsplit.le, hsplit.ge]

/-! ## The tool itself -/

/-- (chapter step S1.2). The three-condition criterion. An earlier review confirms
that this statement needs no repair, and gives the two-regime endgame:

* if `(α + ε)² ≤ 2 M L`, gives `κ ≤ 2M(α+ε)L/((α+ε)² + 2ML)`, and `α ≤ κ` forces
  `α((α+ε)² + 2ML) ≤ 2M(α+ε)L`; letting `ε → 0` gives `α³ ≤ 0`;
* if `(α + ε)² > 2 M L`, the unconditional estimates give `κ ≤ √(ML/2) < (α+ε)/2`, so
  `α ≤ κ < (α+ε)/2`, that is `α < ε`.

Either way `α = 0`, and `f ≥ 0` then gives `f → 0`. -/
theorem tendsto_zero_of_three_conditions {f : ℝ → ℝ} {L K B : ℝ}
    (hnonneg : ∀ x : ℝ, 0 ≤ f x) (hbdd : ∀ x : ℝ, f x ≤ B)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    (havg : limsup (fun x : ℝ => f x) atTop ≤
      limsup (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, f v) atTop)
    (hint : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → f v ≠ 0) →
      (∫ v in a..b, f v) ≤ K) :
    Tendsto f atTop (𝓝 0) := by
  -- normalize the two constants so that they are positive
  set L' : ℝ := max L 1 with hL'def
  set K' : ℝ := max K 1 with hK'def
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlip' : ∀ x y : ℝ, |f x - f y| ≤ L' * |x - y| := by
    intro x y
    refine (hlip x y).trans ?_
    have hLL : L ≤ L' := le_max_left _ _
    nlinarith [abs_nonneg (x - y)]
  have hint' : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ v : ℝ, a < v → v < b → f v ≠ 0) →
      (∫ v in a..b, f v) ≤ K' := fun a b h1 h2 h3 => (hint a b h1 h2 h3).trans (le_max_left _ _)
  have hcont : Continuous f := Stage1bAux.continuous_of_chord hL'pos.le hlip'
  have hbddU : IsBoundedUnder (· ≤ ·) atTop f := isBoundedUnder_of ⟨B, hbdd⟩
  have hcobU : IsCoboundedUnder (· ≤ ·) atTop f :=
    isCoboundedUnder_le_of_eventually_le atTop (x := 0) (by filter_upwards with x using hnonneg x)
  have hbddL : IsBoundedUnder (· ≥ ·) atTop f := isBoundedUnder_of ⟨0, hnonneg⟩
  set α : ℝ := limsup f atTop with hαdef
  have hα0 : 0 ≤ α :=
    le_limsup_of_frequently_le (Frequently.of_forall fun x => hnonneg x) hbddU
  have hess : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, f x ≤ α + ε := by
    intro ε hε
    filter_upwards [eventually_lt_of_limsup_lt (show α < α + ε by linarith) hbddU] with x hx
    exact hx.le
  -- the two regimes of the endgame
  have hα : α ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    set ε : ℝ := min (α / 2) (α ^ 3 / (4 * K' * L')) with hεdef
    have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
    have hεα : ε ≤ α / 2 := min_le_left _ _
    have hεK : ε ≤ α ^ 3 / (4 * K' * L') := min_le_right _ _
    rcases le_or_gt ((α + ε) ^ 2) (2 * K' * L') with hcase | hcase
    · -- the regime the repaired S1.2d covers
      have h5 := average_le_of_gaps_essential (W := f) (B := α) (K := L') (M := K')
        hL'pos hcon hK'pos hcont hnonneg hess hlip' hint' ε hεpos hcase
      have hden : 0 < (α + ε) ^ 2 + 2 * K' * L' := by positivity
      have hαle : α ≤ 2 * K' * (α + ε) * L' / ((α + ε) ^ 2 + 2 * K' * L') := le_trans havg h5
      rw [le_div_iff₀ hden] at hαle
      have h1 : α * (α + ε) ^ 2 ≤ 2 * K' * L' * ε := by linarith [hαle]
      have h2 : 2 * K' * L' * ε ≤ α ^ 3 / 2 := by
        have := mul_le_mul_of_nonneg_left hεK (by positivity : (0 : ℝ) ≤ 2 * K' * L')
        calc 2 * K' * L' * ε ≤ 2 * K' * L' * (α ^ 3 / (4 * K' * L')) := by linarith
          _ = α ^ 3 / 2 := by field_simp; ring
      have h3 : α ^ 3 ≤ α * (α + ε) ^ 2 := by
        nlinarith [mul_pos (mul_pos hcon hcon) hεpos, mul_pos hcon (mul_pos hεpos hεpos)]
      nlinarith [pow_pos hcon 3]
    · -- the complementary regime, where the unconditional estimates already suffice
      have hsqrt := tail_integral_le_sqrt (W := f) (K := L') (M := K') hL'pos hK'pos hlip' hint'
      have hκ : limsup (fun x : ℝ => (1 / x) * ∫ v in (0 : ℝ)..x, f v) atTop ≤
          Real.sqrt (K' * L' / 2) := by
        refine limsup_average_le (D := K') hnonneg ?_
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx using hsqrt x hx
      have hlt : Real.sqrt (K' * L' / 2) < (α + ε) / 2 := by
        have h1 : K' * L' / 2 < ((α + ε) / 2) ^ 2 := by nlinarith
        calc Real.sqrt (K' * L' / 2) < Real.sqrt (((α + ε) / 2) ^ 2) :=
              Real.sqrt_lt_sqrt (by positivity) h1
          _ = (α + ε) / 2 := Real.sqrt_sq (by positivity)
      have : α < (α + ε) / 2 := lt_of_le_of_lt (le_trans havg hκ) hlt
      linarith
  have hliminf : (0 : ℝ) ≤ liminf f atTop :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hbdd) (Eventually.of_forall hnonneg)
  exact tendsto_of_le_liminf_of_limsup_le hliminf hα hbddU hbddL

end SelbergPNT
