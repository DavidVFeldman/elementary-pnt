/-
ElementaryPNT.Stage4aAux — auxiliary development for `ElementaryPNT.Stage4a`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage5Aux
import ElementaryPNT.Stage4aCheb

open Filter Topology MeasureTheory

namespace SelbergPNT
namespace Stage4aAux

/-- The chapter's `ψ` satisfies `ψ(x) ≤ 2x`, by the identification with Mathlib's. -/
theorem psi_le_two_mul {x : ℝ} (hx : 0 ≤ x) : psi x ≤ 2 * x := by
  rw [ElementaryPNT.psi_eq_chebyshevPsi]
  exact Stage4aCheb.psi_le_two_mul hx

/-- `|R(u)| ≤ u` for `u > 0`: the lower half is `ψ ≥ 0`, the upper half is `ψ(u) ≤ 2u`. -/
theorem abs_R_le_self {u : ℝ} (hu : 0 < u) : |R u| ≤ u := by
  rw [abs_le]
  have h1 : 0 ≤ psi u := Stage5Aux.psi_nonneg u
  have h2 : psi u ≤ 2 * u := psi_le_two_mul hu.le
  constructor <;> simp only [R] <;> linarith

/-- `|R(u)/u| ≤ 1` for `u > 0`. -/
theorem abs_R_div_le_one {u : ℝ} (hu : 0 < u) : |R u / u| ≤ 1 := by
  rw [abs_div, abs_of_pos hu, div_le_one hu]
  exact abs_R_le_self hu

/-- `|S(y)| ≤ |y − 2|` for `y > 0`, directly from the integrand bound. -/
theorem abs_S_le_abs_sub_two {y : ℝ} (hy : 0 < y) : |S y| ≤ |y - 2| := by
  have hbound : ∀ u ∈ Set.uIoc (2 : ℝ) y, ‖R u / u‖ ≤ 1 := by
    intro u hu
    have hu0 : 0 < u := by
      have : min (2 : ℝ) y < u := by
        rw [Set.uIoc_eq_union] at hu
        rcases hu with hu | hu
        · exact lt_of_le_of_lt (min_le_left _ _) hu.1
        · exact lt_of_le_of_lt (min_le_right _ _) hu.1
      have : (0 : ℝ) < min 2 y := lt_min (by norm_num) hy
      linarith [this]
    rw [Real.norm_eq_abs]
    exact abs_R_div_le_one hu0
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (2 : ℝ)) (b := y)
    (C := 1) hbound
  simpa [S, Real.norm_eq_abs] using this

/-- `|S(y)| ≤ y` for `y ≥ 1`. -/
theorem abs_S_le_self {y : ℝ} (hy : 1 ≤ y) : |S y| ≤ y := by
  have h := abs_S_le_abs_sub_two (by linarith : (0 : ℝ) < y)
  rcases le_or_gt 2 y with h2 | h2
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - 2)] at h; linarith
  · rw [abs_of_nonpos (by linarith : y - 2 ≤ 0)] at h; linarith

/-- Additivity of `S` away from the origin: `S b − S a = ∫_a^b R(u)/u du`. -/
theorem S_sub_S_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    S b - S a = ∫ u in a..b, R u / u := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (Stage5Aux.intervalIntegrable_R_div (a := (2 : ℝ)) (b := a) (by norm_num) ha)
    (Stage5Aux.intervalIntegrable_R_div (a := a) (b := b) ha hb)
  rw [S, S, ← h]
  ring

/-- `S` is `1`-Lipschitz away from the origin. -/
theorem abs_S_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : |S b - S a| ≤ |b - a| := by
  have hbound : ∀ u ∈ Set.uIoc a b, ‖R u / u‖ ≤ 1 := by
    intro u hu
    have hmin : min a b < u := by
      rw [Set.uIoc_eq_union] at hu
      rcases hu with hu | hu
      · exact lt_of_le_of_lt (min_le_left _ _) hu.1
      · exact lt_of_le_of_lt (min_le_right _ _) hu.1
    have hu0 : 0 < u := lt_of_lt_of_le (lt_min ha hb) hmin.le
    rw [Real.norm_eq_abs]
    exact abs_R_div_le_one hu0
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1) hbound
  rw [S_sub_S_pos ha hb]
  simpa [Real.norm_eq_abs] using this

/-- Half of the Lipschitz bound for `W`, with the two points ordered. -/
theorem abs_W_sub_le_of_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    |W x - W y| ≤ 2 * (x - y) := by
  set a : ℝ := Real.exp x with hadef
  set b : ℝ := Real.exp y with hbdef
  have hb1 : (1 : ℝ) ≤ b := Real.one_le_exp hy
  have hab : b ≤ a := Real.exp_le_exp.2 hyx
  have ha1 : (1 : ℝ) ≤ a := le_trans hb1 hab
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  -- the algebraic split
  have hsplit : W x - W y = (S a - S b) / a + S b * (1 / a - 1 / b) := by
    simp only [W, ← hadef, ← hbdef]
    field_simp
    ring
  -- the two pieces
  have hone : |(S a - S b) / a| ≤ (a - b) / a := by
    rw [abs_div, abs_of_pos ha0]
    have h1 : |S a - S b| ≤ |a - b| := abs_S_sub_le hb0 ha0
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)] at h1
    gcongr
  have htwo : |S b * (1 / a - 1 / b)| ≤ (a - b) / a := by
    rw [abs_mul]
    have h1 : |S b| ≤ b := abs_S_le_self hb1
    have hnn : (0 : ℝ) ≤ (a - b) / (a * b) :=
      div_nonneg (by linarith) (by positivity)
    have h2 : |1 / a - 1 / b| = (a - b) / (a * b) := by
      rw [show (1 / a - 1 / b) = -((a - b) / (a * b)) by field_simp; ring, abs_neg,
        abs_of_nonneg hnn]
    rw [h2]
    calc |S b| * ((a - b) / (a * b)) ≤ b * ((a - b) / (a * b)) :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ = (a - b) / a := by field_simp
  -- `(a − b)/a = 1 − e^{y−x} ≤ x − y`
  have hexp : (a - b) / a ≤ x - y := by
    have hdiv : b / a = Real.exp (y - x) := by
      rw [hadef, hbdef, ← Real.exp_sub]
    have h2 : (a - b) / a = 1 - b / a := by field_simp
    rw [h2, hdiv]
    linarith [Real.add_one_le_exp (y - x)]
  calc |W x - W y| = |(S a - S b) / a + S b * (1 / a - 1 / b)| := by rw [hsplit]
    _ ≤ |(S a - S b) / a| + |S b * (1 / a - 1 / b)| := abs_add_le _ _
    _ ≤ (a - b) / a + (a - b) / a := by linarith [hone, htwo]
    _ ≤ 2 * (x - y) := by linarith [hexp]

/-- `|W|` is `2`-Lipschitz on `[0,∞)`. -/
theorem abs_W_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : |W x - W y| ≤ 2 * |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    exact abs_W_sub_le_of_le hy h
  · rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_sub_comm]
    have := abs_W_sub_le_of_le hx h
    linarith

end Stage4aAux
end SelbergPNT
