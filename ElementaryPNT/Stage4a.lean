/-
ElementaryPNT.Stage4a — Stage 4, the uniform bounds and the Lipschitz condition.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage1b
import ElementaryPNT.Stage4aAux

open Filter Topology

namespace SelbergPNT

/-! ## The two uniform bounds -/

/-- (chapter step S4.3a). `|R(u)| ≤ u` for `u > 0`.

Proof: `Chebyshev.psi_le_const_mul_self` gives `ψ(u) ≤ (log 4)u`, and `log 4 − 1 < 1`, so
`−1 ≤ R(u)/u ≤ log 4 − 1 < 1`. Round 8's `selbergPsi_eq_chebyshevPsi` bridges the two `ψ`s.

**The route is wrong and the repair is in `ElementaryPNT/Stage4aCheb.lean`.** Mathlib's
`Chebyshev.psi_le_const_mul_self` gives `ψ(u) ≤ (log 4 + 4)u`, not `ψ(u) ≤ (log 4)u`, and
`log 4 + 4 − 1 > 1`, so it does not prove this statement. The statement is nevertheless true: it
needs `ψ(u) ≤ 2u`, which `Stage4aCheb.psi_le_two_mul` proves from Mathlib's sharper
`Chebyshev.psi_le` for `u ≥ 400` and by four explicit bands below `400`. See `CENSUS.md`. -/
theorem abs_R_le (u : ℝ) (hu : 0 < u) : |R u| ≤ u := Stage4aAux.abs_R_le_self hu

/-- (chapter step S4.3a). `|S(y)| ≤ y − 2` for `y ≥ 2`, hence `|S(y)|/y ≤ 1`, hence
`limsup |S(y)|/y ≤ 1`. An earlier review notes that this needs no tail splitting. -/
theorem abs_S_le (y : ℝ) (hy : 2 ≤ y) : |S y| ≤ y - 2 := by
  have h := Stage4aAux.abs_S_le_abs_sub_two (by linarith : (0 : ℝ) < y)
  rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - 2)] at h

theorem limsup_abs_S_div_le_one : limsup (fun y : ℝ => |S y| / y) atTop ≤ 1 := by
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun y : ℝ => |S y| / y) :=
    isCoboundedUnder_le_of_eventually_le atTop (x := 0) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      positivity)
  refine limsup_le_of_le hcob ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  have hy0 : (0 : ℝ) < y := by linarith
  rw [div_le_one hy0]
  have := abs_S_le y hy
  linarith

/-- R12-3. `|W(x)| ≤ 1` for `x ≥ 0`, from with `y = eˣ ≥ 1`; for `1 ≤ y ≤ 2`,
`S(y) = 2 − y ∈ [0,1]` , so the bound holds there too. -/
theorem abs_W_le_one (x : ℝ) (hx : 0 ≤ x) : |W x| ≤ 1 := by
  have he1 : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have he0 : (0 : ℝ) < Real.exp x := Real.exp_pos x
  rw [W, abs_div, abs_of_pos he0, div_le_one he0]
  exact Stage4aAux.abs_S_le_self he1

/-! ## Lipschitz -/

/-- (chapter step S4.2a). `S` is Lipschitz with constant `1` on `[2,∞)`: `|S y − S y'| ≤ |y − y'|`.
Proof: `S y − S y' = ∫_{y'}^{y} R(u)/u du` and `|R(u)/u| ≤ 1` by R12-1. -/
theorem S_lipschitz (y y' : ℝ) (hy : 2 ≤ y) (hy' : 2 ≤ y') : |S y - S y'| ≤ |y - y'| :=
  Stage4aAux.abs_S_sub_le (by linarith) (by linarith)

/-- (chapter step S4.2)`). `|W|` is Lipschitz on `[0,∞)`.

An earlier review refutes the global statement: for `u ≤ log 2`, `W(u) = 2e^{−u} − 1`, which blows up
as `u → −∞`. On `[0,∞)` the docstring route works: `W(x) = S(eˣ)/eˣ`, so
`W'(x) = R(eˣ)/eˣ − W(x)`, and both terms are bounded by `1` (R12-1, R12-3), giving `L = 2`;
`| |a| − |b| | ≤ |a − b|` then transfers the bound to `|W|`.

If the mean-value route is awkward in Lean, `|S(eˣ) − S(e^y)| ≤ |eˣ − e^y|` (R12-4) plus the
elementary `|e^{−x} − e^{−y}| ≤ |x − y|` for `x, y ≥ 0` is an alternative.

The route used is the second one, in `Stage4aAux.abs_W_sub_le_of_le`: the mean-value route needs
`S` to be differentiable, which it is not, `R` being discontinuous at every prime power. -/
theorem W_lipschitz_nonneg :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |(|W x| - |W y|)| ≤ L * |x - y| := by
  refine ⟨2, by norm_num, fun x y hx hy => ?_⟩
  exact le_trans (abs_abs_sub_abs_le_abs_sub _ _) (Stage4aAux.abs_W_sub_le hx hy)

/-- The truncation the chain consumes . -/
noncomputable def Wtr (x : ℝ) : ℝ := |W (max x 0)|

/-- (chapter step S4.2). `Wtr` is nonnegative, bounded by `1`, and globally
Lipschitz. Proof: `max · 0` is `1`-Lipschitz, then R12-5, R12-3. -/
theorem Wtr_properties :
    (∀ x : ℝ, 0 ≤ Wtr x) ∧ (∀ x : ℝ, Wtr x ≤ 1) ∧
      ∃ L : ℝ, 0 < L ∧ ∀ x y : ℝ, |Wtr x - Wtr y| ≤ L * |x - y| := by
  refine ⟨fun x => abs_nonneg _, fun x => abs_W_le_one _ (le_max_right x 0), 2, by norm_num,
    fun x y => ?_⟩
  have h1 : |Wtr x - Wtr y| ≤ |W (max x 0) - W (max y 0)| :=
    abs_abs_sub_abs_le_abs_sub _ _
  have h2 : |W (max x 0) - W (max y 0)| ≤ 2 * |max x 0 - max y 0| :=
    Stage4aAux.abs_W_sub_le (le_max_right x 0) (le_max_right y 0)
  have h3 : |max x 0 - max y 0| ≤ |x - y| := abs_max_sub_max_le_abs x y 0
  linarith

/-- R12-7. The truncation changes neither the averages nor the gaps on `[0,∞)`, so the hypotheses
of for `Wtr` follow from the corresponding facts for `|W|`. Proof: `max x 0 = x` for
`x ≥ 0`, and `Wtr` is constant on `(−∞,0]`. -/
theorem Wtr_agrees :
    (∀ x : ℝ, 0 ≤ x → Wtr x = |W x|) ∧
    (∀ x : ℝ, 0 < x → (∫ v in (0 : ℝ)..x, Wtr v) = ∫ v in (0 : ℝ)..x, |W v|) ∧
    limsup Wtr atTop = limsup (fun x : ℝ => |W x|) atTop := by
  have hpt : ∀ x : ℝ, 0 ≤ x → Wtr x = |W x| := by
    intro x hx
    rw [Wtr, max_eq_left hx]
  refine ⟨hpt, fun x hx => ?_, ?_⟩
  · refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [Set.uIcc_of_le hx.le] at hv
    exact hpt v hv.1
  · refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx using hpt x hx

/-! ## The integral form of Mertens -/

/-- (chapter step S4.0). `∫₂^x ψ(u)/u² du = O(log x)`.

Chapter route: `∑_{n ≤ x} Λ(n)/n = ψ(x)/x + ∫₂^x ψ(u)/u² du` up to `O(1)` — compare the jumps at
integers and the derivatives between them, or use Mathlib's Abel summation as an earlier stage did for
`sum_vonMangoldt_mul_log` — and then Mertens  together with `ψ(x) = O(x)` .

This identity is used only in Stage 4c, but it is elementary and independent of the rest of
Stage 4, and this is the natural place to record it.

The route used is an earlier review shortcut: `ψ(u) ≤ 2u` gives `0 ≤ ψ(u)/u² ≤ 2/u`, and
`∫₂^x 2/u du = 2 log(x/2) ≤ 2 log x`. The identity with `∑ Λ(n)/n` is needed only for the matching
lower bound, which the statement does not ask for. -/
theorem integral_psi_div_sq_isBigO :
    (fun x : ℝ => ∫ u in (2 : ℝ)..x, psi u / u ^ 2) =O[atTop] (fun x : ℝ => Real.log x) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hne : ∀ u ∈ Set.uIcc (2 : ℝ) x, u ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le hx] at hu
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)
  have hg : IntervalIntegrable (fun u : ℝ => 2 / u) MeasureTheory.volume 2 x :=
    (ContinuousOn.div continuousOn_const continuousOn_id hne).intervalIntegrable
  have hbound : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc (2 : ℝ) x → ‖psi t / t ^ 2‖ ≤ 2 / t := by
    filter_upwards with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1.le
    have h1 : 0 ≤ psi t := Stage5Aux.psi_nonneg t
    have h2 : psi t ≤ 2 * t := Stage4aAux.psi_le_two_mul ht0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le hx hbound hg
  have hnz : (0 : ℝ) ∉ Set.uIcc (2 : ℝ) x := fun h => hne 0 h rfl
  have hval : (∫ u in (2 : ℝ)..x, 2 / u) = 2 * Real.log (x / 2) := by
    rw [show (fun u : ℝ => 2 / u) = fun u : ℝ => 2 * (1 / u) by funext u; ring]
    rw [intervalIntegral.integral_const_mul, integral_one_div hnz]
  rw [hval] at hle
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsplit : Real.log (x / 2) = Real.log x - Real.log 2 :=
    Real.log_div hx0.ne' (by norm_num)
  simp only [Real.norm_eq_abs] at hle ⊢
  rw [abs_of_nonneg hlogx]
  rw [hsplit] at hle
  linarith

end SelbergPNT
