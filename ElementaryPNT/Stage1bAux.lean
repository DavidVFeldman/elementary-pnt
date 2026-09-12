/-
ElementaryPNT.Stage1bAux — auxiliary development for `ElementaryPNT.Stage1b`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs

open Filter Topology MeasureTheory

namespace SelbergPNT
namespace Stage1bAux

/-- The chord condition makes `W` Lipschitz, hence continuous. -/
theorem continuous_of_chord {W : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) : Continuous W := by
  have h : LipschitzWith K.toNNReal W := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq, Real.coe_toNNReal _ hK] using hchord x y
  exact h.continuous

/-- The triangular bound on a gap: a nonnegative `W` vanishing at `a` and satisfying the chord
condition has `∫_a^b W ≤ K(b−a)²/2`. -/
theorem integral_le_triangle {W : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hzero : W a = 0) (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) :
    (∫ x in a..b, W x) ≤ K * (b - a) ^ 2 / 2 := by
  have hWc : Continuous W := continuous_of_chord hK hchord
  have key : (∫ x in a..b, W x) ≤ ∫ x in a..b, K * (x - a) := by
    refine intervalIntegral.integral_mono_on hab (hWc.intervalIntegrable a b)
      ((by fun_prop : Continuous fun x : ℝ => K * (x - a)).intervalIntegrable a b) ?_
    intro x hx
    have h := hchord x a
    rw [hzero, sub_zero] at h
    calc W x ≤ |W x| := le_abs_self _
      _ ≤ K * |x - a| := h
      _ = K * (x - a) := by rw [abs_of_nonneg (by linarith [hx.1])]
  have heval : (∫ x in a..b, K * (x - a)) = K * (b - a) ^ 2 / 2 := by
    have h : (∫ x in a..b, (x - a)) = (b - a) ^ 2 / 2 := by
      rw [intervalIntegral.integral_comp_sub_right (fun x => x) a, integral_id]
      ring
    rw [intervalIntegral.integral_const_mul, h]
    ring
  linarith [heval ▸ key]

/-- On `[a,b]`, a nonnegative `W` vanishing at `a`, bounded by `B` there and with the chord
condition, lies under `min (K(x−a)) B`. This is with the boundedness hypothesis localized
to the gap. -/
theorem integral_le_integral_min {W : ℝ → ℝ} {a b B K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hzero : W a = 0) (hbdd : ∀ v : ℝ, v ∈ Set.Icc a b → W v ≤ B)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) :
    (∫ x in a..b, W x) ≤ ∫ x in a..b, min (K * (x - a)) B := by
  have hWc : Continuous W := continuous_of_chord hK hchord
  refine intervalIntegral.integral_mono_on hab (hWc.intervalIntegrable a b)
    ((by fun_prop : Continuous fun x : ℝ => min (K * (x - a)) B).intervalIntegrable a b) ?_
  intro x hx
  refine le_min ?_ (hbdd x hx)
  have h := hchord x a
  rw [hzero, sub_zero] at h
  calc W x ≤ |W x| := le_abs_self _
    _ ≤ K * |x - a| := h
    _ = K * (x - a) := by rw [abs_of_nonneg (by linarith [hx.1])]

/-- The evaluation of the comparison integral; this is R11-2, proved here because
`gap_integral_le_mul` needs it. -/
theorem integral_min_ramp_eval {a b B K : ℝ} (hab : a ≤ b) (hK : 0 < K) (hB : 0 < B) :
    (∫ x in a..b, min (K * (x - a)) B) =
      if b - a ≤ B / K then K * (b - a) ^ 2 / 2 else B * (b - a) - B ^ 2 / (2 * K) := by
  have hramp : ∀ p q : ℝ, (∫ x in p..q, K * (x - a)) = K * ((q - a) ^ 2 - (p - a) ^ 2) / 2 := by
    intro p q
    have h : (∫ x in p..q, (x - a)) = ((q - a) ^ 2 - (p - a) ^ 2) / 2 := by
      rw [intervalIntegral.integral_comp_sub_right (fun x => x) a, integral_id]
      try ring
    rw [intervalIntegral.integral_const_mul, h]
    try ring
  have hcont : Continuous fun x : ℝ => min (K * (x - a)) B := by fun_prop
  split_ifs with h
  · have heq : Set.EqOn (fun x : ℝ => min (K * (x - a)) B) (fun x : ℝ => K * (x - a))
        (Set.uIcc a b) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hle : K * (x - a) ≤ B := by
        have hxa : x - a ≤ B / K := le_trans (by linarith [hx.2]) h
        calc K * (x - a) ≤ K * (B / K) := by nlinarith
          _ = B := by field_simp
      simp [min_eq_left hle]
    rw [intervalIntegral.integral_congr heq, hramp a b]
    ring
  · push_neg at h
    set c := a + B / K with hcdef
    have hBK : 0 < B / K := by positivity
    have hac : a ≤ c := by simp [hcdef]; positivity
    have hcb : c ≤ b := by simp [hcdef]; linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable a c) (hcont.intervalIntegrable c b)]
    have h1 : (∫ x in a..c, min (K * (x - a)) B) = B ^ 2 / (2 * K) := by
      have heq : Set.EqOn (fun x : ℝ => min (K * (x - a)) B) (fun x : ℝ => K * (x - a))
          (Set.uIcc a c) := by
        intro x hx
        rw [Set.uIcc_of_le hac] at hx
        have hxa : x - a ≤ B / K := by simp [hcdef] at hx; linarith [hx.2]
        have hle : K * (x - a) ≤ B := by
          calc K * (x - a) ≤ K * (B / K) := by nlinarith
            _ = B := by field_simp
        simp [min_eq_left hle]
      rw [intervalIntegral.integral_congr heq, hramp a c, hcdef]
      field_simp
      ring
    have h2 : (∫ x in c..b, min (K * (x - a)) B) = B * (b - c) := by
      have heq : Set.EqOn (fun x : ℝ => min (K * (x - a)) B) (fun _ : ℝ => B) (Set.uIcc c b) := by
        intro x hx
        rw [Set.uIcc_of_le hcb] at hx
        have hxa : B / K ≤ x - a := by simp [hcdef] at hx; linarith [hx.1]
        have hle : B ≤ K * (x - a) := by
          calc B = K * (B / K) := by field_simp
            _ ≤ K * (x - a) := by nlinarith
        simp [min_eq_right hle]
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [h1, h2, hcdef]
    field_simp
    ring

/-- with the boundedness hypothesis localized to the gap, and in multiplicative form. -/
theorem gap_integral_le_mul {W : ℝ → ℝ} {a b B K M : ℝ} (hab : a < b) (hK : 0 < K) (hB : 0 < B)
    (hM : 0 < M) (hBM : B ^ 2 ≤ 2 * M * K) (hzero : W a = 0)
    (hbdd : ∀ v : ℝ, v ∈ Set.Icc a b → W v ≤ B)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) (hgap : (∫ x in a..b, W x) ≤ M) :
    (∫ x in a..b, W x) ≤ 2 * M * B * K / (B ^ 2 + 2 * M * K) * (b - a) := by
  have ht : 0 < b - a := by linarith
  have hden : 0 < B ^ 2 + 2 * M * K := by positivity
  have hbound := integral_le_integral_min hab.le hK.le hzero hbdd hchord
  rw [integral_min_ramp_eval hab.le hK hB] at hbound
  split_ifs at hbound with hcase
  · -- short gap: the triangular estimate, which never exceeds `B/2 ≤ c`
    have h : K * (b - a) ≤ B := by
      rw [le_div_iff₀ hK] at hcase; linarith
    refine hbound.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    have h1 : (K * (b - a) ^ 2 / 2) * (B ^ 2 + 2 * M * K) ≤ (K * (b - a) ^ 2 / 2) * (4 * M * K) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 2 * M * K * (b - a) * (K * (b - a)) ≤ 2 * M * K * (b - a) * B :=
      mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [h1, h2]
  · rcases le_or_gt (2 * K * B * (b - a)) (B ^ 2 + 2 * M * K) with hshort | hlong
    · -- the trapezoidal estimate, increasing in the length, below the crossover
      refine hbound.trans ?_
      have h2K : (0 : ℝ) < 2 * K := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hden, ← sub_nonneg,
        show 2 * M * B * K * (b - a) - (B * (b - a) - B ^ 2 / (2 * K)) * (B ^ 2 + 2 * M * K)
          = (B ^ 2 * (B ^ 2 + 2 * M * K - 2 * K * B * (b - a))) / (2 * K) by field_simp; ring]
      apply div_nonneg _ h2K.le
      nlinarith [sq_nonneg B]
    · -- the gap estimate, decreasing in the length, above the crossover
      refine hgap.trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hden]
      nlinarith [mul_pos hM ht, mul_pos hK hB]

/-- The unconditional gap estimate, with no `B`: the triangular bound `Kℓ²/2` and the gap bound
`M` cross at `ℓ = √(2M/K)`, where both equal `√(MK/2)·ℓ`. -/
theorem gap_integral_le_sqrt {W : ℝ → ℝ} {a b K M : ℝ} (hab : a < b) (hK : 0 < K) (hM : 0 < M)
    (hzero : W a = 0)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) (hgap : (∫ x in a..b, W x) ≤ M) :
    (∫ x in a..b, W x) ≤ Real.sqrt (M * K / 2) * (b - a) := by
  have ht : 0 < b - a := by linarith
  set s := Real.sqrt (M * K / 2) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = M * K / 2 := Real.sq_sqrt (by positivity)
  rcases le_or_gt (K * (b - a) / 2) s with h | h
  · have tri := integral_le_triangle hab.le hK.le hzero hchord
    nlinarith [tri, ht]
  · refine hgap.trans ?_
    nlinarith [hspos, hs2, h, ht, hK]

end Stage1bAux
end SelbergPNT
