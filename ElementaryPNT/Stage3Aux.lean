/-
ElementaryPNT.Stage3Aux — auxiliary development for `ElementaryPNT.Stage3`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1

open Filter Topology

namespace SelbergPNT

/-! ## Factorials: `log ⌊x⌋! = x log x − x + O(log x)`

The chapter quotes Stirling, but the two-sided bound with error `O(log n)` is elementary: compare
`∑_{k ≤ n} log k` with `n log n − n + 1 = ∫_1^n log t dt`. The comparison is an induction on `n`
whose step is `n log (1 + 1/n) ≤ 1 ≤ (n+1) log (1 + 1/n)`, and both of those come from
`log t ≤ t − 1`. -/

/-- `log n! = ∑_{k ≤ n} log k`. -/
theorem log_factorial_eq_sum_log (n : ℕ) :
    Real.log (Nat.factorial n) = ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos n).ne')]
    push_cast
    ring

/-- The induction step of the elementary Stirling bound: `n log (1 + 1/n) ≤ 1 ≤
(n+1) log (1 + 1/n)`. -/
theorem log_succ_step {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ 1 ∧
      1 ≤ ((n : ℝ) + 1) * (Real.log (n + 1) - Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log ((n + 1) / n) ≤ ((n : ℝ) + 1) / n - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((n : ℝ) / (n + 1)) ≤ (n : ℝ) / (n + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h1
  rw [Real.log_div (by positivity) (by positivity)] at h2
  constructor
  · have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    rw [he] at h1
    calc (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ n * (1 / n) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  · have he : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1)) := by field_simp; ring
    rw [he] at h2
    have h3 : 1 / ((n : ℝ) + 1) ≤ Real.log (n + 1) - Real.log n := by linarith
    calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / (n + 1)) := by field_simp
      _ ≤ ((n : ℝ) + 1) * (Real.log (n + 1) - Real.log n) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Lower half of the elementary Stirling bound: `n log n − n + 1 ≤ log n!`. -/
theorem le_log_factorial_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (Nat.factorial n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hstep := (log_succ_step hn).1
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos n).ne')]
    push_cast
    push_cast at ih hstep
    nlinarith [ih, hstep]

/-- Upper half of the elementary Stirling bound: `log n! ≤ n log n − n + 1 + log n`. -/
theorem log_factorial_le_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hstep := (log_succ_step hn).2
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos n).ne')]
    push_cast
    push_cast at ih hstep
    nlinarith [ih, hstep]

/-- Passing from the integer `⌊x⌋` to the real `x` in `t ↦ t log t − t` costs at most `log x`:
the function increases, and by no more than `(x − m) log x` on `[m, x]`. -/
theorem xlogx_bounds {x : ℝ} (hx : 1 ≤ x) (m : ℕ) (hm1 : 1 ≤ m) (hmx : (m : ℝ) ≤ x)
    (hxm : x < (m : ℝ) + 1) :
    (m : ℝ) * Real.log m - m ≤ x * Real.log x - x ∧
      x * Real.log x - x ≤ (m : ℝ) * Real.log m - m + Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hup : Real.log x - Real.log m ≤ x / m - 1 := by
    have := Real.log_le_sub_one_of_pos (x := x / m) (by positivity)
    rwa [Real.log_div (ne_of_gt hx0) (ne_of_gt hm0)] at this
  have hlow : Real.log m - Real.log x ≤ (m : ℝ) / x - 1 := by
    have := Real.log_le_sub_one_of_pos (x := (m : ℝ) / x) (by positivity)
    rwa [Real.log_div (ne_of_gt hm0) (ne_of_gt hx0)] at this
  have hlogx : 1 - 1 / x ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
    rw [Real.log_div (by norm_num) (ne_of_gt hx0), Real.log_one] at this
    linarith
  have hA : x * (Real.log m - Real.log x) ≤ (m : ℝ) - x := by
    have h := mul_le_mul_of_nonneg_left hlow (le_of_lt hx0)
    have he : x * ((m : ℝ) / x - 1) = (m : ℝ) - x := by field_simp
    linarith [he ▸ h]
  have hB : x - 1 ≤ x * Real.log x := by
    have h := mul_le_mul_of_nonneg_left hlogx (le_of_lt hx0)
    have he : x * (1 - 1 / x) = x - 1 := by field_simp
    linarith [he ▸ h]
  constructor
  · have h1 : (m : ℝ) * (x * (Real.log m - Real.log x)) ≤ (m : ℝ) * ((m : ℝ) - x) :=
      mul_le_mul_of_nonneg_left hA (le_of_lt hm0)
    have h2 : (x - m) * (x - 1) ≤ (x - m) * (x * Real.log x) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have h3 : (0 : ℝ) ≤ (x - m) * ((m : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    have goalx : x * ((m : ℝ) * Real.log m - m) ≤ x * (x * Real.log x - x) := by nlinarith
    exact le_of_mul_le_mul_left goalx hx0
  · have h1 : (m : ℝ) * (Real.log x - Real.log m) ≤ m * (x / m - 1) :=
      mul_le_mul_of_nonneg_left hup (le_of_lt hm0)
    have h2 : (m : ℝ) * (x / m - 1) = x - m := by field_simp
    rw [h2] at h1
    nlinarith [h1, hL0, hxm]

/-- `log ⌊x⌋! = x log x − x + O(log x)`, in the explicit form `|·| ≤ log x + 1` for `x ≥ 1`. -/
theorem abs_log_factorial_floor_sub_xlogx_le {x : ℝ} (hx : 1 ≤ x) :
    |Real.log (Nat.factorial ⌊x⌋₊) - (x * Real.log x - x)| ≤ Real.log x + 1 := by
  set m := ⌊x⌋₊ with hm
  have hm1 : 1 ≤ m := (Nat.one_le_floor_iff x).2 hx
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlogm : Real.log m ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1) hmx
  obtain ⟨hb1, hb2⟩ := xlogx_bounds hx m hm1 hmx hxm
  have hf1 := le_log_factorial_of_one_le hm1
  have hf2 := log_factorial_le_of_one_le hm1
  rw [abs_le]
  constructor <;> linarith

/-! ## Harmonic numbers -/

/-- `|H_n − log n − γ| ≤ 1/n` for `n ≥ 1`: Mathlib's two monotone sequences
`harmonic n − log (n+1) < γ < harmonic n − log n` bracket `γ`, and the gap is
`log (1 + 1/n) ≤ 1/n`. -/
theorem abs_harmonic_sub_log_sub_gamma_le {n : ℕ} (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : n ≠ 0 := by omega
  have h1 : Real.eulerMascheroniConstant < (harmonic n : ℝ) - Real.log n := by
    have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    simpa [Real.eulerMascheroniSeq', hne] using this
  have h2 : (harmonic n : ℝ) - Real.log (n + 1) < Real.eulerMascheroniConstant := by
    have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    simpa [Real.eulerMascheroniSeq] using this
  have h3 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith [he ▸ h]
  rw [abs_le]
  constructor <;> linarith

/-! ## Elementary estimates -/

/-- `log y ≤ 4 y^{1/4}` for `y ≥ 1`, written with two square roots. -/
theorem log_le_four_mul_sqrt_sqrt {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ 4 * Real.sqrt (Real.sqrt y) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have h1 : Real.log (Real.sqrt (Real.sqrt y)) = Real.log y / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg y), Real.log_sqrt hy0]; ring
  have h2 : Real.log (Real.sqrt (Real.sqrt y)) ≤ Real.sqrt (Real.sqrt y) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [h1] at h2
  linarith

/-- `∑_{k ≤ m} k^{-1/2} ≤ 2 √m`, by induction: `2√(m+1) − 2√m ≥ 1/√(m+1)`. -/
theorem sum_one_div_sqrt_le (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, 1 / Real.sqrt k ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hstep : 1 / Real.sqrt ((m : ℝ) + 1) ≤ 2 * Real.sqrt ((m : ℝ) + 1) - 2 * Real.sqrt m := by
      have hpos : (0 : ℝ) < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      rw [div_le_iff₀ hpos]
      have hmul : Real.sqrt m * Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) + 1 / 2 := by
        rw [← Real.sqrt_mul (by positivity)]
        have h := Real.sqrt_le_sqrt
          (show (m : ℝ) * ((m : ℝ) + 1) ≤ ((m : ℝ) + 1 / 2) ^ 2 by nlinarith)
        rwa [Real.sqrt_sq (by positivity)] at h
      have hsq : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      nlinarith [hmul, hsq]
    push_cast
    push_cast at ih
    linarith

/-- A sum over `Icc 0 m` of an arithmetic function vanishing at `0` is a sum over `Icc 1 m`. -/
theorem sum_Icc_zero_eq_sum_Icc_one {m : ℕ} (f : ℕ → ℝ) (h0 : f 0 = 0) :
    ∑ k ∈ Finset.Icc 0 m, f k = ∑ k ∈ Finset.Icc 1 m, f k := by
  refine (Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)).symm
  · simp only [Finset.mem_Icc] at *; omega
  · simp only [Finset.mem_Icc] at hk hk'
    have hk0 : k = 0 := by omega
    rw [hk0, h0]

/-! ## `ψ` -/

theorem psi_nonneg (x : ℝ) : 0 ≤ psi x := by
  rw [ElementaryPNT.psi_eq_chebyshevPsi]
  exact Chebyshev.psi_nonneg x

/-- Chebyshev's upper bound, in the explicit form used below (the `psi_isBigO`, with the
constant made explicit). -/
theorem psi_le_const_mul {x : ℝ} (hx : 0 ≤ x) : psi x ≤ (Real.log 4 + 4) * x := by
  rw [ElementaryPNT.psi_eq_chebyshevPsi]
  exact Chebyshev.psi_le_const_mul_self hx

/-- `∑_{n ≤ x} ψ(x/n) = log ⌊x⌋!`, the Chebyshev identity in the form Stage 3 uses.
Proof: the hyperbola reindexing of an earlier stage turns the left side into `∑_{N ≤ x} ∑_{d ∣ N} Λ(d)`,
and `∑_{d ∣ N} Λ(d) = log N`. -/
theorem sum_psi_div_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, psi (x / n) = Real.log (Nat.factorial ⌊x⌋₊) := by
  set m := ⌊x⌋₊ with hm
  have hexp : ∀ n ∈ Finset.Icc 1 m, psi (x / n)
      = ∑ k ∈ Finset.Icc 1 (m / n), ArithmeticFunction.vonMangoldt k := by
    intro n _
    rw [psi, show ⌊x / (n : ℝ)⌋₊ = m / n by rw [Nat.floor_div_natCast, hm]]
  rw [Finset.sum_congr rfl hexp,
    sum_Icc_sum_Icc_div_eq_sum_divisors m (fun _ k => ArithmeticFunction.vonMangoldt k),
    log_factorial_eq_sum_log]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.sum_div_divisors n ArithmeticFunction.vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_sum

/-- `∑_{n ≤ x} Λ(n) ψ(x/n) = ∑_{N ≤ x} ∑_{d ∣ N} Λ(d) Λ(N/d)`, again by the hyperbola
reindexing. -/
theorem sum_vonMangoldt_mul_psi_div (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * psi (x / n)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors,
          ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d) := by
  set m := ⌊x⌋₊ with hm
  have hexp : ∀ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n * psi (x / n)
      = ∑ k ∈ Finset.Icc 1 (m / n),
          ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt k := by
    intro n _
    rw [psi, show ⌊x / (n : ℝ)⌋₊ = m / n by rw [Nat.floor_div_natCast, hm], Finset.mul_sum]
  rw [Finset.sum_congr rfl hexp,
    sum_Icc_sum_Icc_div_eq_sum_divisors m
      (fun n k => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt k)]

/-- `∫₁^x ψ(t)/t dt = O(x)`, explicitly, from `ψ(t) ≤ (log 4 + 4) t`. -/
theorem abs_integral_psi_div_le {x : ℝ} (hx : 1 ≤ x) :
    |∫ t in (1 : ℝ)..x, psi t / t| ≤ (Real.log 4 + 4) * x := by
  have hbound : ∀ t ∈ Set.uIoc (1 : ℝ) x, ‖psi t / t‖ ≤ Real.log 4 + 4 := by
    intro t ht
    rw [Set.uIoc_of_le hx] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one (le_of_lt ht.1)
    have h1 : psi t ≤ (Real.log 4 + 4) * t := psi_le_const_mul ht0.le
    have h2 : 0 ≤ psi t := psi_nonneg t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ht0]
    linarith
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at hint
  have hx1 : |x - 1| ≤ x := by rw [abs_of_nonneg (by linarith)]; linarith
  have hc : 0 ≤ Real.log 4 + 4 := by positivity
  calc |∫ t in (1 : ℝ)..x, psi t / t| ≤ (Real.log 4 + 4) * |x - 1| := hint
    _ ≤ (Real.log 4 + 4) * x := by nlinarith

end SelbergPNT
