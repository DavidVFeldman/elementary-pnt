/-
ElementaryPNT.Stage4cStep3 — auxiliary development for `ElementaryPNT.Stage4c`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage3
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4cAux
import ElementaryPNT.Stage4cStep2

open Filter Topology

namespace SelbergPNT

namespace Stage4cStep3

/-- The Abel-summation estimate: `∑_{m ≤ y} (Λ₂(m) − 2 log m) |S(y/m)| = O(y log y)`. -/
theorem sum_Lambda2_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (Lambda2 m - 2 * Real.log m) * |S (y / m)| ≤ C * y * Real.log y := by
  obtain ⟨Cs, hCs, hA⟩ := Stage4cAux.selberg_second_const
  refine ⟨4 * Cs, by positivity, fun y hy => ?_⟩
  have hy0 : (0:ℝ) < y := by linarith
  have hlog2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlog0 : (0:ℝ) < Real.log y := by linarith
  set M := ⌊y⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast by linarith : ((1:ℕ):ℝ) ≤ y)
  have hMy : (M : ℝ) ≤ y := Nat.floor_le (le_of_lt hy0)
  have hyM : y < (M : ℝ) + 1 := Nat.lt_floor_add_one y
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M = N + 1 := ⟨M - 1, by omega⟩
  have hNcast : ((M : ℕ) : ℝ) = (N : ℝ) + 1 := by rw [hN]; push_cast; ring
  have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hMR : (0:ℝ) < (N : ℝ) + 1 := by linarith
  have hMyR : ((N : ℝ) + 1) ≤ y := by rw [← hNcast]; exact hMy
  have hyMR : y < ((N : ℝ) + 1) + 1 := by rw [← hNcast]; exact hyM
  have habel := Stage4cAux.abel_sum_Icc (fun m => Lambda2 m - 2 * Real.log m)
    (fun m => |S (y / m)|) N
  rw [hN, habel]
  push_cast
  -- the boundary term
  have hbdry : (∑ m ∈ Finset.Icc 1 (N + 1), (Lambda2 m - 2 * Real.log m))
      * |S (y / ((N : ℝ) + 1))| ≤ 2 * Cs * y := by
    have h1 : |∑ m ∈ Finset.Icc 1 (N + 1), (Lambda2 m - 2 * Real.log m)|
        ≤ Cs * ((N : ℝ) + 1) := by
      have h := hA (N + 1) (by omega)
      have hc : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hc] at h
      exact h
    have hle1 : (1:ℝ) ≤ y / ((N : ℝ) + 1) := by
      rw [le_div_iff₀ hMR]; linarith
    have hle2 : y / ((N : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ hMR]; linarith
    have h2 : |S (y / ((N : ℝ) + 1))| ≤ 2 := Stage4cAux.abs_S_le_two (by linarith) hle2
    calc (∑ m ∈ Finset.Icc 1 (N + 1), (Lambda2 m - 2 * Real.log m))
          * |S (y / ((N : ℝ) + 1))|
        ≤ |∑ m ∈ Finset.Icc 1 (N + 1), (Lambda2 m - 2 * Real.log m)|
            * |S (y / ((N : ℝ) + 1))| :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ ≤ (Cs * ((N : ℝ) + 1)) * 2 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ 2 * Cs * y := by nlinarith
  -- the sum of the variations
  have hvar : ∑ m ∈ Finset.Icc 1 N, (∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)) *
      (|S (y / m)| - |S (y / ((m : ℝ) + 1))|) ≤ Cs * y * Real.log y := by
    have hterm : ∀ m ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)) *
          (|S (y / m)| - |S (y / ((m : ℝ) + 1))|) ≤ Cs * y * (1 / ((m : ℝ) + 1)) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
      have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
      have hA' : |∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)| ≤ Cs * m := hA m hm1
      have h1 : |(|S (y / m)| - |S (y / ((m : ℝ) + 1))|)|
          ≤ |S (y / m) - S (y / ((m : ℝ) + 1))| := abs_abs_sub_abs_le_abs_sub _ _
      have h2 : |S (y / m) - S (y / ((m : ℝ) + 1))| ≤ |y / m - y / ((m : ℝ) + 1)| :=
        Stage4aAux.abs_S_sub_le (by positivity) (by positivity)
      have h3 : |y / (m : ℝ) - y / ((m : ℝ) + 1)| = y / ((m : ℝ) * ((m : ℝ) + 1)) := by
        rw [abs_of_nonneg (by
          rw [sub_nonneg]
          gcongr
          linarith)]
        field_simp
        ring
      have hvar' : |(|S (y / m)| - |S (y / ((m : ℝ) + 1))|)|
          ≤ y / ((m : ℝ) * ((m : ℝ) + 1)) := by
        rw [← h3]; exact le_trans h1 h2
      have hsimp : (Cs * (m : ℝ)) * (y / ((m : ℝ) * ((m : ℝ) + 1)))
          = Cs * y * (1 / ((m : ℝ) + 1)) := by
        field_simp
      calc (∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)) *
            (|S (y / m)| - |S (y / ((m : ℝ) + 1))|)
          ≤ |(∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)) *
              (|S (y / m)| - |S (y / ((m : ℝ) + 1))|)| := le_abs_self _
        _ = |∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)| *
              |(|S (y / m)| - |S (y / ((m : ℝ) + 1))|)| := abs_mul _ _
        _ ≤ (Cs * (m : ℝ)) * (y / ((m : ℝ) * ((m : ℝ) + 1))) :=
            mul_le_mul hA' hvar' (abs_nonneg _) (by positivity)
        _ = Cs * y * (1 / ((m : ℝ) + 1)) := hsimp
    calc ∑ m ∈ Finset.Icc 1 N, (∑ j ∈ Finset.Icc 1 m, (Lambda2 j - 2 * Real.log j)) *
          (|S (y / m)| - |S (y / ((m : ℝ) + 1))|)
        ≤ ∑ m ∈ Finset.Icc 1 N, Cs * y * (1 / ((m : ℝ) + 1)) := Finset.sum_le_sum hterm
      _ = Cs * y * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / ((m : ℝ) + 1) := by rw [Finset.mul_sum]
      _ ≤ Cs * y * Real.log ((N : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left (Stage4cAux.sum_one_div_succ_le N) (by positivity)
      _ ≤ Cs * y * Real.log y :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hMR hMyR) (by positivity)
  have hyb : 2 * Cs * y ≤ 3 * Cs * y * Real.log y := by
    nlinarith [mul_pos hCs hy0]
  linarith [hbdry, hvar]

/-- (chapter step S4.1c). There is `C₃ > 0` with

  `|S(y)|(log y)² ≤ 2 ∑_{m ≤ y} |S(y/m)| log m + C₃ y log y`  for `y ≥ 2`. -/
theorem abs_S_log_sq_le_sum : ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ y : ℝ, 2 ≤ y →
    |S y| * (Real.log y) ^ 2 ≤
      2 * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, |S (y / m)| * Real.log m) + C₃ * y * Real.log y := by
  obtain ⟨C₂, hC₂, h2⟩ := Stage4cStep2.S_log_sq_eq
  obtain ⟨C, hC, h3⟩ := sum_Lambda2_sub_le
  refine ⟨C₂ + C, by linarith, fun y hy => ?_⟩
  have hy0 : (0:ℝ) < y := by linarith
  have hlog0 : (0:ℝ) ≤ Real.log y := Real.log_nonneg (by linarith)
  set M := ⌊y⌋₊ with hM
  set Sig : ℝ := ∑ m ∈ Finset.Icc 1 M,
    (ArithmeticFunction.vonMangoldt m * Real.log m -
      ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
        ArithmeticFunction.vonMangoldt (m / d)) * S (y / m) with hSig
  have hb1 : |S y * (Real.log y) ^ 2 + Sig| ≤ C₂ * y * Real.log y := h2 y hy
  -- the triangle inequality, term by term
  have hb2 : |Sig| ≤ ∑ m ∈ Finset.Icc 1 M, Lambda2 m * |S (y / m)| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hlogm : (0:ℝ) ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
    have hconv : (0:ℝ) ≤ ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
        ArithmeticFunction.vonMangoldt (m / d) :=
      Finset.sum_nonneg fun d _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg
    have hLam : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt m * Real.log m :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlogm
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Lambda2]
    rcases abs_cases (ArithmeticFunction.vonMangoldt m * Real.log m -
      ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d *
        ArithmeticFunction.vonMangoldt (m / d)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have hsplit : ∑ m ∈ Finset.Icc 1 M, Lambda2 m * |S (y / m)|
      = (∑ m ∈ Finset.Icc 1 M, (Lambda2 m - 2 * Real.log m) * |S (y / m)|)
        + 2 * ∑ m ∈ Finset.Icc 1 M, |S (y / m)| * Real.log m := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hb3 := h3 y hy
  have habs : |S y| * (Real.log y) ^ 2 = |S y * (Real.log y) ^ 2| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.log y) ^ 2)]
  have hfin : |S y * (Real.log y) ^ 2| ≤ |S y * (Real.log y) ^ 2 + Sig| + |Sig| := by
    have := abs_sub (S y * (Real.log y) ^ 2 + Sig) Sig
    simpa using this
  rw [habs]
  rw [hsplit] at hb2
  linarith

end Stage4cStep3

end SelbergPNT
