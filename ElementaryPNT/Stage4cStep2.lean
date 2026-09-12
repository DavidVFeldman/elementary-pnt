/-
ElementaryPNT.Stage4cStep2 — auxiliary development for `ElementaryPNT.Stage4c`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage1Aux
import ElementaryPNT.Stage3
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4cAux
import ElementaryPNT.Stage4cStep1

open Filter Topology

namespace SelbergPNT

namespace Stage4cStep2

/-- The hyperbola reindexing, applied to the double sum of R14-2: summing `Λ(k) Λ(n) S(y/(kn))`
over `k ≤ y`, `n ≤ y/k` is summing `(Λ∗Λ)(m) S(y/m)` over `m ≤ y`. -/
theorem double_sum_eq (y : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt k *
        ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n)
      = ∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
          (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
            ArithmeticFunction.vonMangoldt (m / d)) * S (y / m) := by
  have hstep1 : (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt k *
        ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n)
      = ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, ∑ n ∈ Finset.Icc 1 (⌊y⌋₊ / k),
          (ArithmeticFunction.vonMangoldt k * ArithmeticFunction.vonMangoldt n *
            S (y / ((k : ℝ) * (n : ℝ)))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.floor_div_natCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [div_div]; ring
  have hstep2 := sum_Icc_sum_Icc_div_eq_sum_divisors ⌊y⌋₊
    (fun k n => ArithmeticFunction.vonMangoldt k * ArithmeticFunction.vonMangoldt n *
      S (y / ((k : ℝ) * (n : ℝ))))
  rw [hstep1, hstep2]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d ∣ m := (Nat.mem_divisors.1 hd).1
  have hcast : ((d : ℝ) * ((m / d : ℕ) : ℝ)) = (m : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdm]
  rw [hcast]

/-- (chapter step S4.1b). There is `C₂ > 0` with

  `|S(y)(log y)² + ∑_{m ≤ y} (Λ(m) log m − (Λ∗Λ)(m)) S(y/m)| ≤ C₂ y log y`  for `y ≥ 2`. -/
theorem S_log_sq_eq : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ y : ℝ, 2 ≤ y →
    |S y * (Real.log y) ^ 2 +
      ∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
        (ArithmeticFunction.vonMangoldt m * Real.log m -
          ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
            ArithmeticFunction.vonMangoldt (m / d)) * S (y / m)|
      ≤ C₂ * y * Real.log y := by
  obtain ⟨C₁, hC₁, hT⟩ := Stage4cStep1.selberg_S_form
  obtain ⟨CM, hCM, hMert⟩ := Stage4cAux.sum_vonMangoldt_div_le
  refine ⟨2 * C₁ + 2 * C₁ * CM, by positivity, fun y hy => ?_⟩
  have hy0 : (0:ℝ) < y := by linarith
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlog2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog0 : (0:ℝ) < Real.log y := by linarith
  set M := ⌊y⌋₊ with hM
  have hkle : ∀ k ∈ Finset.Icc 1 M, (1:ℝ) ≤ y / k := by
    intro k hk
    simp only [Finset.mem_Icc, hM] at hk
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk.1
    have hky : (k:ℝ) ≤ y := le_trans (by exact_mod_cast hk.2) (Nat.floor_le (le_of_lt hy0))
    rw [le_div_iff₀ hk0]
    linarith
  -- the two families
  set T1 : ℝ := ∑ n ∈ Finset.Icc 1 M, S (y / n) * ArithmeticFunction.vonMangoldt n with hT1
  set A : ℝ := ∑ k ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt k *
      (S (y / k) * Real.log (y / k) +
        ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n) with hA
  have hAsplit : A = (Real.log y * T1
        - ∑ k ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt k * Real.log k * S (y / k))
      + ∑ m ∈ Finset.Icc 1 M,
          (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
            ArithmeticFunction.vonMangoldt (m / d)) * S (y / m) := by
    have hsplit : A = (∑ k ∈ Finset.Icc 1 M,
          ArithmeticFunction.vonMangoldt k * (S (y / k) * Real.log (y / k)))
        + ∑ k ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt k *
            ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n := by
      rw [hA, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, double_sum_eq y]
    congr 1
    rw [hT1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hk0 : (k:ℝ) ≠ 0 := by
      have : (0:ℝ) < k := by exact_mod_cast hk1
      exact ne_of_gt this
    rw [Real.log_div (ne_of_gt hy0) hk0]
    ring
  -- the identity
  have hid : S y * (Real.log y) ^ 2 +
      ∑ m ∈ Finset.Icc 1 M,
        (ArithmeticFunction.vonMangoldt m * Real.log m -
          ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
            ArithmeticFunction.vonMangoldt (m / d)) * S (y / m)
      = (S y * Real.log y + T1) * Real.log y - A := by
    have hsplit2 : ∑ m ∈ Finset.Icc 1 M,
        (ArithmeticFunction.vonMangoldt m * Real.log m -
          ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
            ArithmeticFunction.vonMangoldt (m / d)) * S (y / m)
        = (∑ m ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt m * Real.log m * S (y / m))
          - ∑ m ∈ Finset.Icc 1 M, (∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
              ArithmeticFunction.vonMangoldt (m / d)) * S (y / m) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsplit2, hAsplit]
    ring
  rw [hid]
  -- the bounds
  have hb1 : |(S y * Real.log y + T1) * Real.log y| ≤ C₁ * y * Real.log y := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hlog0)]
    have := hT y (by linarith)
    nlinarith [abs_nonneg (S y * Real.log y + T1)]
  have hb2 : |A| ≤ C₁ * y * Real.log y + C₁ * CM * y := by
    have hterm : ∀ k ∈ Finset.Icc 1 M,
        |ArithmeticFunction.vonMangoldt k *
          (S (y / k) * Real.log (y / k) +
            ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n)|
          ≤ C₁ * y * (ArithmeticFunction.vonMangoldt k / k) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
      have h := hT (y / k) (hkle k hk)
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hΛ : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
      have hfin : ArithmeticFunction.vonMangoldt k * (C₁ * (y / k))
          = C₁ * y * (ArithmeticFunction.vonMangoldt k / k) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      calc ArithmeticFunction.vonMangoldt k *
            |S (y / k) * Real.log (y / k) +
              ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n|
          ≤ ArithmeticFunction.vonMangoldt k * (C₁ * (y / k)) := by
            exact mul_le_mul_of_nonneg_left h hΛ
        _ = C₁ * y * (ArithmeticFunction.vonMangoldt k / k) := hfin
    calc |A| ≤ ∑ k ∈ Finset.Icc 1 M,
          |ArithmeticFunction.vonMangoldt k *
            (S (y / k) * Real.log (y / k) +
              ∑ n ∈ Finset.Icc 1 ⌊y / k⌋₊, S (y / k / n) * ArithmeticFunction.vonMangoldt n)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 M, C₁ * y * (ArithmeticFunction.vonMangoldt k / k) :=
          Finset.sum_le_sum hterm
      _ = C₁ * y * ∑ k ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt k / k) := by
          rw [Finset.mul_sum]
      _ ≤ C₁ * y * (Real.log y + CM) := by
          have := hMert y (by linarith)
          have hpos : (0:ℝ) ≤ C₁ * y := by positivity
          exact mul_le_mul_of_nonneg_left this hpos
      _ = C₁ * y * Real.log y + C₁ * CM * y := by ring
  have hfinal := abs_sub (a := (S y * Real.log y + T1) * Real.log y) (b := A)
  have hyle : C₁ * CM * y ≤ 2 * C₁ * CM * y * Real.log y := by
    have h1 : (1:ℝ) ≤ 2 * Real.log y := by linarith
    nlinarith [mul_pos (mul_pos hC₁ hCM) hy0]
  nlinarith [hfinal, hb1, hb2, hyle]

end Stage4cStep2

end SelbergPNT
