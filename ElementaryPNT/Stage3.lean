/-
ElementaryPNT.Stage3 — Stage 3: Selberg's inequality, in both forms.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage3Aux

open Filter Topology

namespace SelbergPNT

/-! ## Stage 3a: the two inputs to Tatuzawa–Iseki -/

/-- `F₁(x) = x − (1 + γ)` for `x ≥ 1`, and `0` below. -/
noncomputable def F1 (x : ℝ) : ℝ := if 1 ≤ x then x - (1 + Real.eulerMascheroniConstant) else 0

/-- `M F (x) = ∑_{n ≤ x} F(x/n)`. -/
noncomputable def Mtr (F : ℝ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F (x / n)

/-- `(M F₁)(x) = x H_{⌊x⌋} − (1+γ)⌊x⌋`, by linearity: every `x/n` with `n ≤ ⌊x⌋` is at least
`1`, so the cutoff in `F₁` never fires. -/
theorem Mtr_F1_eq {x : ℝ} (hx : 1 ≤ x) :
    Mtr F1 x = x * (harmonic ⌊x⌋₊ : ℝ) - (1 + Real.eulerMascheroniConstant) * (⌊x⌋₊ : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set m := ⌊x⌋₊ with hm
  have hterm : ∀ n ∈ Finset.Icc 1 m, F1 (x / n)
      = x * ((n : ℝ))⁻¹ - (1 + Real.eulerMascheroniConstant) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
    rw [F1, if_pos ((one_le_div hn0).2 hnx)]
    field_simp
  rw [Mtr, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  have hharm : (harmonic m : ℝ) = ∑ i ∈ Finset.Icc 1 m, ((i : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  rw [hharm]
  simp [Nat.card_Icc]
  ring

/-- `(M F₁)(x) = x log x − x + O(1)`, explicitly: the error is at most `5` for `x ≥ 2`. -/
theorem abs_Mtr_F1_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |Mtr F1 x - (x * Real.log x - x)| ≤ 5 := by
  have hx0 : (0 : ℝ) < x := by linarith
  set m := ⌊x⌋₊ with hm
  have hm2 : 2 ≤ m := by
    rw [hm]; exact Nat.le_floor (by exact_mod_cast hx)
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hmeq := Mtr_F1_eq (x := x) (by linarith)
  have hharm := abs_harmonic_sub_log_sub_gamma_le (n := m) (by omega)
  have hgam0 : 0 < Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant; linarith
  have hgam : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hd1 : x * (Real.log x - Real.log m) ≤ 3 / 2 ∧ 0 ≤ x * (Real.log x - Real.log m) := by
    constructor
    · have h := Real.log_le_sub_one_of_pos (x := x / m) (by positivity)
      rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hm0)] at h
      have h2 : x * (Real.log x - Real.log m) ≤ x * (x / m - 1) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hx0)
      have h3 : x * (x / m - 1) ≤ 3 / 2 := by
        rw [show x * (x / m - 1) = (x * (x - m)) / m by field_simp, div_le_iff₀ hm0]
        nlinarith
      linarith
    · have hmono : Real.log m ≤ Real.log x := Real.log_le_log hm0 hmx
      nlinarith
  have hd2 : |x * ((harmonic m : ℝ) - Real.log m - Real.eulerMascheroniConstant)| ≤ 3 / 2 := by
    rw [abs_mul, abs_of_pos hx0]
    have h1 : x * |(harmonic m : ℝ) - Real.log m - Real.eulerMascheroniConstant| ≤ x * (1 / m) :=
      mul_le_mul_of_nonneg_left hharm (le_of_lt hx0)
    have h2 : x * (1 / (m : ℝ)) ≤ 3 / 2 := by
      rw [show x * (1 / (m : ℝ)) = x / m by ring, div_le_iff₀ hm0]
      nlinarith
    linarith
  have hd2' := abs_le.1 hd2
  rw [hmeq, abs_le]
  constructor <;> nlinarith [hd1.1, hd1.2, hd2'.1, hd2'.2]

/-- (§"Selberg's inequality", first computation). `(M F₁)(x) = log ⌊x⌋! + O(log x)`.

Chapter proof: by linearity, `(M F₁)(x) = x ∑_{n ≤ x} 1/n − (1+γ)⌊x⌋`, and with
`∑_{n ≤ x} 1/n = log x + γ + O(1/x)` (Mathlib: `Real.tendsto_sum_range_one_div_nat_succ_sub_log`
and the bounds in `Mathlib/NumberTheory/Harmonic/Bounds.lean`) and `⌊x⌋ = x − {x}` this is
`x log x − x + O(1)`, which is `log ⌊x⌋! + O(log x)` by Stirling
(`Mathlib/Analysis/SpecialFunctions/Stirling.lean`, or the elementary two-sided bound
`n log n − n ≤ log n! ≤ n log n`). -/
theorem Mtr_F1_sub_log_factorial_isBigO :
    (fun x : ℝ => Mtr F1 x - Real.log (Nat.factorial ⌊x⌋₊)) =O[atTop] (fun x : ℝ => Real.log x) := by
  refine Asymptotics.isBigO_iff.2 ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog1 : (1 : ℝ) < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ x := by linarith
  have h1 : |Mtr F1 x - (x * Real.log x - x)| ≤ 5 := abs_Mtr_F1_sub_le (by linarith)
  have h2 : |Real.log (Nat.factorial ⌊x⌋₊) - (x * Real.log x - x)| ≤ Real.log x + 1 :=
    abs_log_factorial_floor_sub_xlogx_le (by linarith)
  have hsplit : Mtr F1 x - Real.log (Nat.factorial ⌊x⌋₊)
      = (Mtr F1 x - (x * Real.log x - x)) - (Real.log (Nat.factorial ⌊x⌋₊)
        - (x * Real.log x - x)) := by ring
  have hb : |Mtr F1 x - Real.log (Nat.factorial ⌊x⌋₊)| ≤ 5 + (Real.log x + 1) := by
    rw [hsplit]
    exact le_trans (abs_sub _ _) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < Real.log x)]
  linarith

/-- `F_S(x) = ψ(x) − (x − (1 + γ))`, the chapter's `F_S`. -/
noncomputable def FS (x : ℝ) : ℝ := psi x - F1 x

/-- On `[1, ∞)`, `F_S(x) = ψ(x) − x + (1 + γ)`. -/
theorem FS_eq {x : ℝ} (hx : 1 ≤ x) : FS x = psi x - x + (1 + Real.eulerMascheroniConstant) := by
  simp only [FS, F1, if_pos hx]; ring

/-- `(M F_S)(x) = log ⌊x⌋! − (M F₁)(x)`. -/
theorem Mtr_FS_eq (x : ℝ) :
    Mtr FS x = Real.log (Nat.factorial ⌊x⌋₊) - Mtr F1 x := by
  rw [Mtr, Mtr, ← sum_psi_div_eq_log_factorial x, ← Finset.sum_sub_distrib]
  rfl

/-- R10-2. `(M F_S)(x) = O(log x)`.

Chapter proof: `(M ψ)(x) = log ⌊x⌋!` — the Chebyshev identity, already available as
`Chebyshev.log_factorial_eq_sum_vonMangoldt_mul_div` in the `contrib` file and as the
same identity inside `Real/Round8Aux.lean` — so `(M F_S)(x) = log ⌊x⌋! − (M F₁)(x)`, and R10-1
applies. The point of the chapter's "coincidence": a complicated function and a simple one have
numerically close transforms. -/
theorem Mtr_FS_isBigO : (fun x : ℝ => Mtr FS x) =O[atTop] (fun x : ℝ => Real.log x) := by
  have h := Mtr_F1_sub_log_factorial_isBigO.neg_left
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  rw [Mtr_FS_eq x]; ring

/-! ## Stage 3b: Selberg's inequality, first form -/

/-- A bound on `M F_S` valid on all of `[1, ∞)`, not merely eventually: this is what the crude
step of needs, since `x/k` ranges down to `1`. -/
theorem abs_Mtr_FS_le {y : ℝ} (hy : 1 ≤ y) : |Mtr FS y| ≤ 7 + Real.log y := by
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  rcases le_or_gt 2 y with hy2 | hy2
  · have h1 := abs_log_factorial_floor_sub_xlogx_le (x := y) (by linarith)
    have h2 := abs_Mtr_F1_sub_le hy2
    rw [Mtr_FS_eq y]
    have h1' := abs_le.1 h1
    have h2' := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith
  · have hfl : ⌊y⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by exact_mod_cast hy, by exact_mod_cast hy2⟩
    have hpsi : psi y = 0 := by rw [psi, hfl]; simp
    have hMtr : Mtr FS y = FS y := by rw [Mtr, hfl]; simp
    have hgam0 : 0 < Real.eulerMascheroniConstant := by
      have := Real.one_half_lt_eulerMascheroniConstant; linarith
    have hgam : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
    rw [hMtr, FS_eq hy, hpsi, abs_le]
    constructor <;> linarith

/-- The crude bound of the chapter: `log y · (M F_S)(y) = O(√y)`, explicitly. -/
theorem abs_log_mul_Mtr_FS_le {y : ℝ} (hy : 1 ≤ y) :
    |Real.log y * Mtr FS y| ≤ 44 * Real.sqrt y := by
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hb := abs_Mtr_FS_le hy
  have hs4 := log_le_four_mul_sqrt_sqrt hy
  have hsq : Real.sqrt (Real.sqrt y) * Real.sqrt (Real.sqrt y) = Real.sqrt y :=
    Real.mul_self_sqrt (Real.sqrt_nonneg y)
  have hss : Real.sqrt (Real.sqrt y) ≤ Real.sqrt y := by
    have h1 : (1 : ℝ) ≤ Real.sqrt y := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hy
    nlinarith [Real.sqrt_nonneg (Real.sqrt y), hsq]
  rw [abs_mul, abs_of_nonneg hlog0]
  calc Real.log y * |Mtr FS y| ≤ Real.log y * (7 + Real.log y) :=
        mul_le_mul_of_nonneg_left hb hlog0
    _ ≤ 44 * Real.sqrt y := by nlinarith [hs4, hsq, hss]

/-- The right-hand side of Tatuzawa–Iseki at `F = F_S` is `O(x)`. -/
theorem abs_tatuzawa_rhs_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) *
      ∑ j ∈ Finset.Icc 1 ⌊x / k⌋₊, FS (x / (k * j))| ≤ 88 * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set m := ⌊x⌋₊ with hm
  have hterm : ∀ k ∈ Finset.Icc 1 m,
      |(ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) *
        ∑ j ∈ Finset.Icc 1 ⌊x / k⌋₊, FS (x / (k * j))|
        ≤ 44 * (Real.sqrt x / Real.sqrt k) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hkx : (k : ℝ) ≤ x := le_trans (by exact_mod_cast hk.2) (Nat.floor_le (by linarith))
    have hxk : 1 ≤ x / k := (one_le_div hk0).2 hkx
    have hinner : ∑ j ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, FS (x / (k * j)) = Mtr FS (x / k) := by
      rw [Mtr]
      exact Finset.sum_congr rfl fun j _ => by rw [div_div]
    rw [hinner, mul_assoc, abs_mul]
    have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
      have hone := ArithmeticFunction.abs_moebius_le_one (n := k)
      have hcast : |(ArithmeticFunction.moebius k : ℝ)|
          = ((|ArithmeticFunction.moebius k| : ℤ) : ℝ) := by push_cast; ring
      rw [hcast]
      exact_mod_cast hone
    have hrest := abs_log_mul_Mtr_FS_le hxk
    rw [Real.sqrt_div (le_of_lt hx0)] at hrest
    calc |(ArithmeticFunction.moebius k : ℝ)| * |Real.log (x / k) * Mtr FS (x / k)|
        ≤ 1 * (44 * (Real.sqrt x / Real.sqrt k)) :=
          mul_le_mul hmu hrest (abs_nonneg _) (by norm_num)
      _ = 44 * (Real.sqrt x / Real.sqrt k) := by ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hrw : ∑ k ∈ Finset.Icc 1 m, 44 * (Real.sqrt x / Real.sqrt k)
      = 44 * Real.sqrt x * ∑ k ∈ Finset.Icc 1 m, 1 / Real.sqrt k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrw]
  have hsum := sum_one_div_sqrt_le m
  have hsm : Real.sqrt m ≤ Real.sqrt x := Real.sqrt_le_sqrt (Nat.floor_le (by linarith))
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (le_of_lt hx0)
  have h44 : (0 : ℝ) ≤ 44 * Real.sqrt x := by positivity
  calc 44 * Real.sqrt x * ∑ k ∈ Finset.Icc 1 m, 1 / Real.sqrt k
      ≤ 44 * Real.sqrt x * (2 * Real.sqrt m) := mul_le_mul_of_nonneg_left hsum h44
    _ ≤ 44 * Real.sqrt x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (by linarith) h44
    _ = 88 * x := by
        rw [show 44 * Real.sqrt x * (2 * Real.sqrt x)
          = 88 * (Real.sqrt x * Real.sqrt x) by ring, hxx]

/-- Passing from `F_S` to `ψ(x) − x` in Selberg's inequality. -/
theorem selberg_first_rewrite {x : ℝ} (hx : 1 ≤ x) :
    (psi x - x) * Real.log x +
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (psi (x / n) - x / n) * ArithmeticFunction.vonMangoldt n
      = (FS x * Real.log x +
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, FS (x / n) * ArithmeticFunction.vonMangoldt n)
        - (1 + Real.eulerMascheroniConstant) * Real.log x
        - (1 + Real.eulerMascheroniConstant) * psi x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpsi : psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := rfl
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, FS (x / n) * ArithmeticFunction.vonMangoldt n
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (psi (x / n) - x / n) * ArithmeticFunction.vonMangoldt n)
        + (1 + Real.eulerMascheroniConstant) * psi x := by
    rw [hpsi, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
    rw [FS_eq ((one_le_div hn0).2 hnx)]
    ring
  rw [hsum, FS_eq hx]
  ring

/-- (§"Selberg's inequality"). Selberg's inequality:
`(ψ(x) − x) log x + ∑_{n ≤ x} (ψ(x/n) − x/n) Λ(n) = O(x)`.

Chapter proof. Apply Tatuzawa–Iseki (`tatuzawa_iseki`) to `F = F_S`. On the right-hand
side, bound `|μ(k)| ≤ 1` and use in the crude form `log(x/k)·(M F_S)(x/k) = O((x/k)^{1/2})`;
then `∑_{k ≤ x} (x/k)^{1/2} = x^{1/2} ∑_{k ≤ x} k^{-1/2} = O(x)`, the inner sum being `O(x^{1/2})`
by comparison with `∫ t^{-1/2}`. That gives
`F_S(x) log x + ∑_{n ≤ x} F_S(x/n) Λ(n) = O(x)`. Finally replace `F_S` by `ψ(x) − x`: the
constant `1 + γ` contributes `O(log x)` in the first term and `(1+γ)ψ(x) = O(x)` in the second,
by Chebyshev (`psi_isBigO`, stage 9). -/
theorem selberg_first :
    (fun x : ℝ => (psi x - x) * Real.log x +
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (psi (x / n) - x / n) * ArithmeticFunction.vonMangoldt n) =O[atTop]
      (fun x : ℝ => x) := by
  refine Asymptotics.isBigO_iff.2 ⟨102, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hTI := tatuzawa_iseki FS x hx
  have hrhs := abs_tatuzawa_rhs_le hx
  have hlhs : |FS x * Real.log x +
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, FS (x / n) * ArithmeticFunction.vonMangoldt n| ≤ 88 * x := by
    rw [hTI]; exact hrhs
  have hlogx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpsi : psi x ≤ (Real.log 4 + 4) * x := psi_le_const_mul (le_of_lt hx0)
  have hpsi0 : 0 ≤ psi x := psi_nonneg x
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hgam : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hgam0 : 0 < Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant; linarith
  rw [selberg_first_rewrite hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
  have hb := abs_le.1 hlhs
  have h1 : |(1 + Real.eulerMascheroniConstant) * Real.log x| ≤ 2 * x := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have h2 : |(1 + Real.eulerMascheroniConstant) * psi x| ≤ 2 * ((Real.log 4 + 4) * x) := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [abs_le]
  constructor <;> nlinarith

/-! ## Stage 3c: the `Λ₂` form -/

/-- (§"Selberg's inequality", the massaging). The intermediate form
`ψ(x) log x + ∑_{n ≤ x} Λ(n) ψ(x/n) = 2x log x + O(x)`.

Chapter proof: in R10-3, `∑_{n ≤ x} (x/n) Λ(n) = x ∑_{n ≤ x} Λ(n)/n = x log x + O(x)` by Mertens
(`mertens`), and `x log x` is the other `x log x`. -/
theorem selberg_psi_form :
    (fun x : ℝ => psi x * Real.log x +
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * psi (x / n))
      - 2 * x * Real.log x) =O[atTop] (fun x : ℝ => x) := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.1 selberg_first
  obtain ⟨C, hC0, hCb⟩ := mertens
  refine Asymptotics.isBigO_iff.2 ⟨c + C, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (2 : ℝ)] with x hc' hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hkey : psi x * Real.log x +
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * psi (x / n))
      - 2 * x * Real.log x
      = ((psi x - x) * Real.log x +
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (psi (x / n) - x / n) * ArithmeticFunction.vonMangoldt n)
        + x * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n) - Real.log x) := by
    have hsum1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (psi (x / n) - x / n) * ArithmeticFunction.vonMangoldt n
        = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * psi (x / n))
          - x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hsum1]
    ring
  have hm := hCb x hx
  have h2 : |x * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n)
      - Real.log x)| ≤ C * x := by
    rw [abs_mul, abs_of_pos hx0, mul_comm]
    exact mul_le_mul_of_nonneg_right hm (le_of_lt hx0)
  have h1 : |(psi x - x) * Real.log x +
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (psi (x / n) - x / n) * ArithmeticFunction.vonMangoldt n|
      ≤ c * x := by
    simpa [Real.norm_eq_abs, abs_of_pos hx0] using hc'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, hkey]
  exact le_trans (abs_add_le _ _) (by linarith)

/-- (§"Selberg's inequality", Abel summation step).
`∑_{n ≤ x} Λ(n) log n = ψ(x) log x − ∫₁^x ψ(t)/t dt`, for `x ≥ 1`.

Chapter proof: both sides vanish at `x = 1`, both are constant between integers, and at an
integer `n` both jump by `Λ(n) log n`. In Lean, `Mathlib/NumberTheory/AbelSummation.lean`
(`sum_mul_eq_sub_integral_mul` and relatives) is the intended route. -/
theorem sum_vonMangoldt_mul_log (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log n =
      psi x * Real.log x - ∫ t in (1 : ℝ)..x, psi t / t := by
  have habel := sum_mul_eq_sub_integral_mul₀ (𝕜 := ℝ) (f := Real.log)
    (c := fun n => ArithmeticFunction.vonMangoldt n) (by simp) x
    (fun t ht => Real.differentiableAt_log
      (by have h1 := ht.1; intro h; rw [h] at h1; linarith))
    (by
      rw [Real.deriv_log']
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      intro t ht
      exact ContinuousAt.continuousWithinAt (continuousAt_inv₀
        (by have h1 := ht.1; intro h; rw [h] at h1; linarith)))
  rw [Real.deriv_log'] at habel
  have h1 : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, Real.log k * ArithmeticFunction.vonMangoldt k
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log n := by
    rw [sum_Icc_zero_eq_sum_Icc_one _ (by simp)]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have h2 : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k = psi t :=
    fun t => sum_Icc_zero_eq_sum_Icc_one _ (by simp)
  rw [h1] at habel
  rw [habel, h2]
  congr 1
  · ring
  · rw [intervalIntegral.integral_of_le hx]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [h2]
    ring

/-- (chapter step S3.2). `∑_{n ≤ x} Λ₂(n) = 2x log x + O(x)`.

Chapter proof: in replace `ψ(x) log x` by `∑_{n ≤ x} Λ(n) log n` using R10-5, the
integral being `O(x)` since `ψ(t)/t = O(1)` (`psi_isBigO`); and unwind
`∑_{n ≤ x} Λ(n) ψ(x/n) = ∑_{mn ≤ x} Λ(m)Λ(n) = ∑_{n ≤ x} ∑_{jk = n} Λ(j)Λ(k)` by the hyperbola
reindexing proved earlier (`Stage1Aux`). -/
theorem selberg_second :
    (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Lambda2 n) - 2 * x * Real.log x) =O[atTop]
      (fun x : ℝ => x) := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.1 selberg_psi_form
  refine Asymptotics.isBigO_iff.2 ⟨c + (Real.log 4 + 4), ?_⟩
  filter_upwards [hc, eventually_ge_atTop (1 : ℝ)] with x hc' hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLam2 : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Lambda2 n)
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log n)
        + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors,
            ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => rfl
  have hkey : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Lambda2 n) - 2 * x * Real.log x
      = (psi x * Real.log x +
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * psi (x / n))
          - 2 * x * Real.log x) - ∫ t in (1 : ℝ)..x, psi t / t := by
    rw [hLam2, sum_vonMangoldt_mul_log x hx, ← sum_vonMangoldt_mul_psi_div x]
    ring
  have hint := abs_integral_psi_div_le hx
  have hc'' : |psi x * Real.log x +
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * psi (x / n))
      - 2 * x * Real.log x| ≤ c * x := by
    simpa [Real.norm_eq_abs, abs_of_pos hx0] using hc'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, hkey]
  refine le_trans (abs_sub _ _) ?_
  linarith

/-- (§"Selberg's inequality", corollary). `∑_{n ≤ x} (Λ₂(n) − 2 log n) = O(x)`.
Chapter proof: `∑_{n ≤ x} log n = x log x + O(x)`, which is `log ⌊x⌋!` again. -/
theorem selberg_second' :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Lambda2 n - 2 * Real.log n)) =O[atTop]
      (fun x : ℝ => x) := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.1 selberg_second
  refine Asymptotics.isBigO_iff.2 ⟨c + 6, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (2 : ℝ)] with x hc' hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hfac := abs_log_factorial_floor_sub_xlogx_le (x := x) (by linarith)
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Lambda2 n - 2 * Real.log n)
      = ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Lambda2 n) - 2 * x * Real.log x)
        + 2 * ((x * Real.log x - x) - Real.log (Nat.factorial ⌊x⌋₊)) + 2 * x := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← log_factorial_eq_sum_log]
    ring
  have hc'' : |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Lambda2 n) - 2 * x * Real.log x| ≤ c * x := by
    simpa [Real.norm_eq_abs, abs_of_pos hx0] using hc'
  have hfac' := abs_le.1 hfac
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, hsum, abs_le]
  have hc''' := abs_le.1 hc''
  constructor <;> nlinarith

end SelbergPNT
