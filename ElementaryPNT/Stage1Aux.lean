/-
ElementaryPNT.Stage1Aux — auxiliary development for `ElementaryPNT.Stage1`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Chebyshev

open Filter Topology Asymptotics

namespace SelbergPNT

/-! ## Factorial estimates -/

/-- `(2m)! ≤ 4^m (m!)²`: the central binomial coefficient is at most `4^m`. -/
theorem two_mul_factorial_le (m : ℕ) :
    (2 * m).factorial ≤ 4 ^ m * (m.factorial * m.factorial) := by
  have hchoose : (2 * m).choose m ≤ 4 ^ m :=
    le_trans (Nat.choose_le_choose m (by omega)) (Nat.choose_middle_le_pow m)
  have hfac : (2 * m).choose m * (m.factorial * m.factorial) = (2 * m).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at this
    rw [← this]; ring
  calc (2 * m).factorial = (2 * m).choose m * (m.factorial * m.factorial) := hfac.symm
    _ ≤ 4 ^ m * (m.factorial * m.factorial) := by
        exact Nat.mul_le_mul_right _ hchoose

/-- `n! ≤ n · 2^n · ((n/2)!)²` for `n ≥ 1`, the integer form of R9-3. -/
theorem factorial_le_mul_pow_two_mul_sq {n : ℕ} (hn : 1 ≤ n) :
    n.factorial ≤ n * 2 ^ n * ((n / 2).factorial * (n / 2).factorial) := by
  set m := n / 2 with hm
  have hcases : n = 2 * m ∨ n = 2 * m + 1 := by omega
  have hbase := two_mul_factorial_le m
  have h4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rcases hcases with h | h
  · calc n.factorial = (2 * m).factorial := by rw [h]
      _ ≤ 4 ^ m * (m.factorial * m.factorial) := hbase
      _ = 2 ^ n * (m.factorial * m.factorial) := by rw [h4, ← h]
      _ ≤ n * 2 ^ n * (m.factorial * m.factorial) := by
          have : 1 * 2 ^ n ≤ n * 2 ^ n := Nat.mul_le_mul_right _ hn
          simp only [one_mul] at this
          exact Nat.mul_le_mul_right _ this
  · have hstep : n.factorial = n * (2 * m).factorial := by
      rw [h]; rw [Nat.factorial_succ]
    calc n.factorial = n * (2 * m).factorial := hstep
      _ ≤ n * (4 ^ m * (m.factorial * m.factorial)) := Nat.mul_le_mul_left _ hbase
      _ = n * 2 ^ (2 * m) * (m.factorial * m.factorial) := by rw [h4]; ring
      _ ≤ n * 2 ^ n * (m.factorial * m.factorial) := by
          have : (2 : ℕ) ^ (2 * m) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)

/-- `log (n!) ≤ n log n`. -/
theorem log_factorial_le (n : ℕ) : Real.log (n.factorial) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc Real.log (n.factorial) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hpos h
    _ = n * Real.log n := by
        rw [Real.log_pow]

/-- `n log n − n ≤ log (n!)` for `n ≥ 1`, from Mathlib's Stirling lower bound. -/
theorem le_log_factorial {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial) := by
  have hstir := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg h2pi
  linarith

/-! ## Mertens' weak form: the two halves -/

/-- Replacing `⌊x/d⌋` by `x/d` in `log ⌊x⌋! = ∑_{d ≤ x} Λ(d) ⌊x/d⌋` costs at most `ψ(x)`, which
Chebyshev's upper bound bounds by `(log 4 + 4) x`. -/
theorem abs_mul_sum_vonMangoldt_div_sub_log_factorial_le {x : ℝ} (hx : 2 ≤ x) :
    |x * (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d / d)
      - Real.log ((⌊x⌋₊).factorial)| ≤ (Real.log 4 + 4) * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  set m := ⌊x⌋₊ with hm
  have hIoc : Finset.Ioc 0 m = Finset.Icc 1 m := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hid := ElementaryPNT.log_factorial_eq_sum_vonMangoldt_mul_div m
  rw [hIoc] at hid
  have hfloor : ∀ d : ℕ, 1 ≤ d → ((m / d : ℕ) : ℝ) = (⌊x / (d : ℝ)⌋₊ : ℝ) := by
    intro d _
    rw [Nat.floor_div_natCast, hm]
  have hdiff : x * (∑ d ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt d / d)
      - Real.log (m.factorial)
      = ∑ d ∈ Finset.Icc 1 m,
          ArithmeticFunction.vonMangoldt d * (x / d - ((m / d : ℕ) : ℝ)) := by
    rw [hid, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hdiff]
  have hbounds : ∀ d ∈ Finset.Icc 1 m,
      0 ≤ ArithmeticFunction.vonMangoldt d * (x / d - ((m / d : ℕ) : ℝ)) ∧
      ArithmeticFunction.vonMangoldt d * (x / d - ((m / d : ℕ) : ℝ))
        ≤ ArithmeticFunction.vonMangoldt d := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    have hdiv0 : (0 : ℝ) ≤ x / d := by positivity
    have hfl := Nat.floor_le hdiv0
    have hfl' := Nat.lt_floor_add_one (x / (d : ℝ))
    rw [hfloor d hd.1]
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    constructor
    · have : 0 ≤ x / d - (⌊x / (d : ℝ)⌋₊ : ℝ) := by linarith
      positivity
    · nlinarith [hΛ]
  have hpsi : ∑ d ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt d ≤ (Real.log 4 + 4) * x := by
    have := Chebyshev.psi_le_const_mul_self (x := x) (by linarith)
    rw [← ElementaryPNT.psi_eq_chebyshevPsi] at this
    simpa [SelbergPNT.psi, hm] using this
  rw [abs_le]
  constructor
  · have h0 : 0 ≤ ∑ d ∈ Finset.Icc 1 m,
        ArithmeticFunction.vonMangoldt d * (x / d - ((m / d : ℕ) : ℝ)) :=
      Finset.sum_nonneg fun d hd => (hbounds d hd).1
    have : 0 ≤ (Real.log 4 + 4) * x := by
      have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith
    linarith
  · calc ∑ d ∈ Finset.Icc 1 m,
        ArithmeticFunction.vonMangoldt d * (x / d - ((m / d : ℕ) : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt d :=
        Finset.sum_le_sum fun d hd => (hbounds d hd).2
    _ ≤ (Real.log 4 + 4) * x := hpsi

/-- `log ⌊x⌋! = x log x + O(x)`, in the explicit form needed for Mertens. -/
theorem abs_log_factorial_floor_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log ((⌊x⌋₊).factorial) - x * Real.log x| ≤ (Real.log 2 + 2) * x := by
  set m := ⌊x⌋₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.one_le_floor_iff]; linarith
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x - 1 < (m : ℝ) := by
    have := Nat.lt_floor_add_one x
    rw [← hm] at this
    linarith
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hlogm_nonneg : 0 ≤ Real.log m := Real.log_nonneg hm1R
  have hlogmx : Real.log m ≤ Real.log x := Real.log_le_log (by linarith) hmx
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogx_le : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < x by linarith)
    linarith
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- upper bound
  have hupper : Real.log (m.factorial) ≤ x * Real.log x := by
    have h1 := log_factorial_le m
    have h2 : (m : ℝ) * Real.log m ≤ x * Real.log x := by
      have : (m : ℝ) * Real.log m ≤ x * Real.log m :=
        mul_le_mul_of_nonneg_right hmx hlogm_nonneg
      nlinarith
    linarith
  -- lower bound
  have hlogm_ge : Real.log x - Real.log 2 ≤ Real.log m := by
    have hhalf : x / 2 ≤ (m : ℝ) := by linarith
    have := Real.log_le_log (show (0:ℝ) < x / 2 by linarith) hhalf
    rwa [Real.log_div (by linarith) (by norm_num)] at this
  have hA : (x - 1) * (Real.log x - Real.log 2) ≤ (m : ℝ) * Real.log m := by
    have h1 : (x - 1) * (Real.log x - Real.log 2) ≤ (x - 1) * Real.log m :=
      mul_le_mul_of_nonneg_left hlogm_ge (by linarith)
    have h2 : (x - 1) * Real.log m ≤ (m : ℝ) * Real.log m :=
      mul_le_mul_of_nonneg_right (by linarith) hlogm_nonneg
    linarith
  have hexp : (x - 1) * (Real.log x - Real.log 2)
      = x * Real.log x - x * Real.log 2 - Real.log x + Real.log 2 := by ring
  have hlower := le_log_factorial hm1
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! ## The two one-sided integral estimates behind Stage 1a -/

/-- If `g(y) ≥ c y` then, `g + id` being monotone, `g` stays above the line of slope `-1` through
`(y, c y)` on `[y, y(1+c)]`, and the integral of `g(u)/u` over that interval is at least the area
of the triangle divided by the right endpoint. -/
theorem integral_ge_of_pos_spike {g : ℝ → ℝ} (hmono : Monotone (fun x : ℝ => g x + x))
    (hloc : ∀ b : ℝ, IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume 2 b)
    {c y : ℝ} (hc : 0 < c) (hy : 2 ≤ y) (hgy : c * y ≤ g y) :
    c ^ 2 * y / (2 * (1 + c))
      ≤ (∫ u in (2 : ℝ)..(y * (1 + c)), g u / u) - ∫ u in (2 : ℝ)..y, g u / u := by
  have hy0 : (0 : ℝ) < y := by linarith
  set Y := y * (1 + c) with hY
  have hyY : y ≤ Y := by nlinarith
  have hY0 : (0 : ℝ) < Y := by nlinarith
  have hint1 : IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume 2 y := hloc y
  have hint2 : IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume y Y := by
    refine (hloc Y).mono_set ?_
    rw [Set.uIcc_of_le hyY, Set.uIcc_of_le (show (2 : ℝ) ≤ Y by linarith)]
    exact Set.Icc_subset_Icc hy le_rfl
  have hsplit : (∫ u in (2 : ℝ)..Y, g u / u) - (∫ u in (2 : ℝ)..y, g u / u)
      = ∫ u in y..Y, g u / u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]; ring
  rw [hsplit]
  have hcmp : ∀ u ∈ Set.Icc y Y, (c * y + y - u) / Y ≤ g u / u := by
    rintro u ⟨hu1, hu2⟩
    have hu0 : (0 : ℝ) < u := by linarith
    have hmu : g y + y ≤ g u + u := hmono hu1
    have hgu : c * y + y - u ≤ g u := by linarith
    have hnum : 0 ≤ c * y + y - u := by
      have : u ≤ y + c * y := by rw [hY] at hu2; linarith [hu2]
      linarith
    rw [div_le_div_iff₀ hY0 hu0]
    nlinarith
  have hlowint : IntervalIntegrable (fun u : ℝ => (c * y + y - u) / Y) MeasureTheory.volume y Y :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hmono_int : (∫ u in y..Y, (c * y + y - u) / Y) ≤ ∫ u in y..Y, g u / u :=
    intervalIntegral.integral_mono_on hyY hlowint hint2 hcmp
  have hprim : (∫ u in y..Y, (c * y + y - u)) = (c * y + y) * (Y - y) - (Y ^ 2 - y ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => c * y + y) (g := fun u : ℝ => u)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  have hcomp : (∫ u in y..Y, (c * y + y - u) / Y) = c ^ 2 * y / (2 * (1 + c)) := by
    rw [intervalIntegral.integral_div, hprim, hY]
    field_simp
    ring
  linarith [hcomp ▸ hmono_int]

/-- The mirror estimate: if `g(y) ≤ -c y` then the integral of `g(u)/u` over `[y(1-c), y]` is at
most `-c² y / 2`. -/
theorem integral_le_of_neg_spike {g : ℝ → ℝ} (hmono : Monotone (fun x : ℝ => g x + x))
    (hloc : ∀ b : ℝ, IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume 2 b)
    {c y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : 2 ≤ y * (1 - c)) (hgy : g y ≤ -(c * y)) :
    (∫ u in (2 : ℝ)..y, g u / u) - (∫ u in (2 : ℝ)..(y * (1 - c)), g u / u)
      ≤ -(c ^ 2 * y / 2) := by
  set Z := y * (1 - c) with hZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hc1' : 1 - c ≤ 1 := by linarith
  have hy0 : (0 : ℝ) < y := by nlinarith
  have hZy : Z ≤ y := by nlinarith
  have hint1 : IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume 2 Z := hloc Z
  have hint2 : IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume Z y := by
    refine (hloc y).mono_set ?_
    rw [Set.uIcc_of_le hZy, Set.uIcc_of_le (show (2 : ℝ) ≤ y by linarith)]
    exact Set.Icc_subset_Icc hy le_rfl
  have hsplit : (∫ u in (2 : ℝ)..y, g u / u) - (∫ u in (2 : ℝ)..Z, g u / u)
      = ∫ u in Z..y, g u / u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]; ring
  rw [hsplit]
  have hcmp : ∀ u ∈ Set.Icc Z y, g u / u ≤ (Z - u) / y := by
    rintro u ⟨hu1, hu2⟩
    have hu0 : (0 : ℝ) < u := by linarith
    have hmu : g u + u ≤ g y + y := hmono hu2
    have hgu : g u ≤ Z - u := by rw [hZ]; linarith
    have hnum : Z - u ≤ 0 := by linarith
    rw [div_le_div_iff₀ hu0 hy0]
    nlinarith
  have hupint : IntervalIntegrable (fun u : ℝ => (Z - u) / y) MeasureTheory.volume Z y :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hmono_int : (∫ u in Z..y, g u / u) ≤ ∫ u in Z..y, (Z - u) / y :=
    intervalIntegral.integral_mono_on hZy hint2 hupint hcmp
  have hprim : (∫ u in Z..y, (Z - u)) = Z * (y - Z) - (y ^ 2 - Z ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => Z) (g := fun u : ℝ => u)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  have hcomp : (∫ u in Z..y, (Z - u) / y) = -(c ^ 2 * y / 2) := by
    rw [intervalIntegral.integral_div, hprim, hZ]
    field_simp
    ring
  linarith [hcomp ▸ hmono_int]

/-! ## The double sum of the Tatuzawa–Iseki identity -/

/-- The hyperbola reindexing: summing over `k ≤ m` and `j ≤ m/k` is summing over the pairs
`(k, j)` with `k j ≤ m`, which are grouped by their product `n = k j` into the divisors of `n`. -/
theorem sum_Icc_sum_Icc_div_eq_sum_divisors (m : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 (m / k), f k j
      = ∑ n ∈ Finset.Icc 1 m, ∑ k ∈ n.divisors, f k (n / k) := by
  classical
  set s : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 * p.2 ≤ m) with hs
  have hcell : ∀ k : ℕ, 1 ≤ k →
      (Finset.Icc 1 m).filter (fun j => k * j ≤ m) = Finset.Icc 1 (m / k) := by
    intro k hk
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, _⟩, hkj⟩
      refine ⟨hj1, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩
      rw [Nat.mul_comm]
      exact hkj
    · rintro ⟨hj1, hj2⟩
      have hkj : j * k ≤ m := (Nat.le_div_iff_mul_le (by omega)).1 hj2
      have hjm : j ≤ m := le_trans (Nat.le_mul_of_pos_right j (by omega)) hkj
      refine ⟨⟨hj1, hjm⟩, ?_⟩
      rw [Nat.mul_comm]
      exact hkj
  have hLHS : ∑ k ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 (m / k), f k j
      = ∑ p ∈ s, f p.1 p.2 := by
    rw [hs, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [← hcell k hk.1, Finset.sum_filter]
  have hmaps : ∀ p ∈ s, p.1 * p.2 ∈ Finset.Icc 1 m := by
    intro p hp
    rw [hs] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    exact Finset.mem_Icc.2 ⟨by nlinarith [hp.1.1.1, hp.1.2.1], hp.2⟩
  have hfib : ∀ n ∈ Finset.Icc 1 m,
      s.filter (fun p => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    ext p
    simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨-, hprod⟩
      exact ⟨hprod, by omega⟩
    · rintro ⟨hprod, -⟩
      have hp1 : 1 ≤ p.1 := by
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · rw [h] at hprod; omega
        · exact h
      have hp2 : 1 ≤ p.2 := by
        rcases Nat.eq_zero_or_pos p.2 with h | h
        · rw [h] at hprod; omega
        · exact h
      have h1 : p.1 ≤ n := hprod ▸ Nat.le_mul_of_pos_right p.1 (by omega)
      have h2 : p.2 ≤ n := hprod ▸ Nat.le_mul_of_pos_left p.2 (by omega)
      exact ⟨⟨⟨⟨hp1, by omega⟩, hp2, by omega⟩, by rw [hprod]; exact hn.2⟩, hprod⟩
  calc ∑ k ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 (m / k), f k j
      = ∑ p ∈ s, f p.1 p.2 := hLHS
    _ = ∑ n ∈ Finset.Icc 1 m, ∑ p ∈ s with p.1 * p.2 = n, f p.1 p.2 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ n ∈ Finset.Icc 1 m, ∑ p ∈ n.divisorsAntidiagonal, f p.1 p.2 := by
        exact Finset.sum_congr rfl fun n hn => by rw [hfib n hn]
    _ = ∑ n ∈ Finset.Icc 1 m, ∑ k ∈ n.divisors, f k (n / k) :=
        Finset.sum_congr rfl fun n _ => Nat.sum_divisorsAntidiagonal f

/-- `∑_{k ∣ n} μ(k) log(x/k) = log x · [n = 1] + Λ(n)`, the arithmetic heart of Tatuzawa–Iseki. -/
theorem sum_divisors_moebius_mul_log_div {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∑ k ∈ n.divisors, (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k)
      = Real.log x * (if n = 1 then 1 else 0) + ArithmeticFunction.vonMangoldt n := by
  have hsplit : ∀ k ∈ n.divisors, (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k)
      = Real.log x * (ArithmeticFunction.moebius k : ℝ)
        - (ArithmeticFunction.moebius k : ℝ) * Real.log k := by
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hk
      positivity
    rw [Real.log_div (ne_of_gt hx) hk0]
    ring
  have hmulog : ∑ k ∈ n.divisors, (ArithmeticFunction.moebius k : ℝ) * Real.log k
      = -ArithmeticFunction.vonMangoldt n := by
    have := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
    simpa [ArithmeticFunction.log_apply] using this
  have hmu : ∑ k ∈ n.divisors, (ArithmeticFunction.moebius k : ℝ)
      = (if n = 1 then 1 else 0) := by
    have hz : ∑ k ∈ n.divisors, ArithmeticFunction.moebius k = (if n = 1 then (1 : ℤ) else 0) := by
      have h := ArithmeticFunction.coe_mul_zeta_apply
        (f := ArithmeticFunction.moebius) (x := n)
      rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at h
      exact h.symm
    rw [← Int.cast_sum, hz]
    split <;> norm_num
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, hmulog, hmu]
  ring

end SelbergPNT
