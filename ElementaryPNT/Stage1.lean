/-
ElementaryPNT.Stage1 — Stage 1a (averages to values), Stage 1c (Chebyshev, Mertens) and Stage 2 (Tatuzawa–Iseki).

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1Aux

open Filter Topology

namespace SelbergPNT

/-! ## Stage 1a: averages to values -/

/-- (chapter step S1.1).
An earlier review showed the blueprint's version vacuous, because its monotonicity
hypothesis failed for the cut-off `R`; this is the abstract form the chapter actually proves.

Chapter proof, in contrapositive form. Suppose `g(x)/x` does not tend to `0`, so for some
`c ∈ (0,1)` either `g(y) > c y` for arbitrarily large `y`, or `g(y) < −c y` for arbitrarily
large `y`. In the first case monotonicity of `g + id` gives `g(x) ≥ (c y + y) − x ≥ 0` on
`[y, y(1+c)]`, whence
`∫_y^{y(1+c)} g(u)/u du ≥ (1/(y(1+c))) ∫_y^{y(1+c)} g(u) du ≥ (1/(y(1+c)))·(cy)²/2 = y c²/(2(1+c))`,
the middle step by the area of the triangle under the line of slope `−1` through `(y, cy)`.
So the quantity `(∫₂^x g(u)/u du)/x` varies by at least `c²/(2(1+c))` on intervals `[y, y(1+c)]`
reaching arbitrarily far out, and cannot converge. The second case is symmetric on
`[y(1−c), y]`, with `−y c²/(2(1−c))`. -/
theorem tendsto_div_of_tendsto_integral_div (g : ℝ → ℝ)
    (hmono : Monotone (fun x : ℝ => g x + x))
    (hloc : ∀ b : ℝ, IntervalIntegrable (fun u : ℝ => g u / u) MeasureTheory.volume 2 b)
    (hS : Tendsto (fun x : ℝ => (∫ u in (2 : ℝ)..x, g u / u) / x) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => g x / x) atTop (𝓝 0) := by
  by_contra hcon
  rw [NormedAddCommGroup.tendsto_nhds_zero] at hcon
  push_neg at hcon
  obtain ⟨ε, hε, hnot⟩ := hcon
  set c : ℝ := min ε (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min hε (by norm_num)
  have hc12 : c ≤ 1 / 2 := min_le_right _ _
  have hc1 : c ≤ 1 := by linarith
  have hfreq : ∃ᶠ x : ℝ in atTop, c ≤ |g x / x| := by
    refine hnot.mono fun x hx => ?_
    simp only [Real.norm_eq_abs] at hx
    exact le_trans (min_le_left _ _) hx
  set δ : ℝ := c ^ 2 / 24 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hSb : ∀ᶠ t : ℝ in atTop, |∫ u in (2 : ℝ)..t, g u / u| ≤ δ * t := by
    have h := (NormedAddCommGroup.tendsto_nhds_zero.1 hS) δ hδ0
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_lt_iff₀ ht0] at ht
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hSb
  set N' : ℝ := max N 0 with hN'def
  have hN'0 : 0 ≤ N' := le_max_right _ _
  have hNN' : N ≤ N' := le_max_left _ _
  obtain ⟨y, hy1, hy2⟩ :=
    (hfreq.and_eventually (eventually_ge_atTop (max 4 (2 * N')))).exists
  have hy4 : (4 : ℝ) ≤ y := le_trans (le_max_left _ _) hy2
  have hyN' : 2 * N' ≤ y := le_trans (le_max_right _ _) hy2
  have hy0 : (0 : ℝ) < y := by linarith
  have habs : c * y ≤ |g y| := by
    rw [abs_div, abs_of_pos hy0] at hy1
    exact (le_div_iff₀ hy0).1 hy1
  rcases le_or_gt 0 (g y) with hsign | hsign
  · -- `g` is large and positive at `y`
    have hgy : c * y ≤ g y := by rwa [abs_of_nonneg hsign] at habs
    have key := integral_ge_of_pos_spike hmono hloc hc0 (by linarith) hgy
    have hb1 := hN (y * (1 + c)) (by nlinarith)
    have hb2 := hN y (by linarith)
    have hb1' := (abs_le.1 hb1).2
    have hb2' := (abs_le.1 hb2).1
    have hY2 : y * (1 + c) ≤ 2 * y := by nlinarith
    have hlow : c ^ 2 * y / 4 ≤ c ^ 2 * y / (2 * (1 + c)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [sq_nonneg c]
    have hdy : δ * (y * (1 + c)) ≤ δ * (2 * y) := by nlinarith
    nlinarith [hlow, key, hb1', hb2', hdy]
  · -- `g` is large and negative at `y`
    have hgy : g y ≤ -(c * y) := by
      rw [abs_of_neg hsign] at habs
      linarith
    have hZ2 : (2 : ℝ) ≤ y * (1 - c) := by nlinarith
    have key := integral_le_of_neg_spike hmono hloc hc0 hc1 hZ2 hgy
    have hZy : y * (1 - c) ≤ y := by nlinarith
    have hZN : N ≤ y * (1 - c) := by nlinarith
    have hb1 := hN y (by linarith)
    have hb2 := hN (y * (1 - c)) hZN
    have hb1' := (abs_le.1 hb1).1
    have hb2' := (abs_le.1 hb2).2
    have hdy : δ * (y * (1 - c)) ≤ δ * y := by nlinarith
    nlinarith [key, hb1', hb2', hdy]

/-- R9-2. The instance needed downstream: `R x + x = ψ x` is monotone, so applies to
`g = R`. Proof: `psi` is monotone (`ElementaryPNT.psi_eq_chebyshevPsi` and
`Chebyshev.psi_mono`, or directly from the definition, the sum being over `Finset.Icc 1 ⌊x⌋₊`
with nonnegative terms). -/
theorem monotone_R_add_id : Monotone (fun x : ℝ => R x + x) := by
  intro a b hab
  have hpsi : psi a ≤ psi b := by
    rw [ElementaryPNT.psi_eq_chebyshevPsi, ElementaryPNT.psi_eq_chebyshevPsi]
    exact Chebyshev.psi_mono hab
  simp only [R]
  linarith

/-! ## Stage 1c: Chebyshev and Mertens -/

/-- (chapter step S1.3).
`log x! − 2 log (x/2)! ≤ x log 2 + log x`, where `x!` means `⌊x⌋!`.

Chapter proof: `(2n)!/(n!)² ≤ 2^{2n}` (the central binomial coefficient counts a subfamily of
all subsets), so `log (2n)! − 2 log n! ≤ 2n log 2`; passing from `2n` to a real `x` costs one
extra jump of `log x`, since `log⌊x⌋!` increases by `log⌊x⌋` as `x` crosses an integer while
`log⌊x/2⌋!` may not move. Mathlib supplies `Nat.choose_middle_le_pow` and
`Nat.choose_mul_factorial_mul_factorial`. -/
theorem log_factorial_sub_two_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log (Nat.factorial ⌊x⌋₊) - 2 * Real.log (Nat.factorial ⌊x / 2⌋₊)
      ≤ x * Real.log 2 + Real.log x := by
  set n := ⌊x⌋₊ with hn
  set m := ⌊x / 2⌋₊ with hmdef
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_floor_iff]
    exact hx
  have hm : m = n / 2 := by
    rw [hmdef, hn, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_div_natCast]
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hfm : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hle : ((n.factorial : ℕ) : ℝ)
      ≤ (n : ℝ) * 2 ^ n * ((m.factorial : ℝ) * (m.factorial : ℝ)) := by
    have := factorial_le_mul_pow_two_mul_sq hn1
    rw [← hm] at this
    exact_mod_cast this
  have key : Real.log (n.factorial)
      ≤ Real.log n + n * Real.log 2 + 2 * Real.log (m.factorial) := by
    have hpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    calc Real.log (n.factorial)
        ≤ Real.log ((n : ℝ) * 2 ^ n * ((m.factorial : ℝ) * (m.factorial : ℝ))) :=
          Real.log_le_log hpos hle
      _ = Real.log n + n * Real.log 2 + 2 * Real.log (m.factorial) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow]
          ring
  have hlogn : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [key, hlogn, hnx, hlog2]

/-- (chapter step S1.4). `ψ(x) = O(x)`.
Mathlib has this in all but name: `Chebyshev.psi_le_const_mul_self`, transported along
`ElementaryPNT.psi_eq_chebyshevPsi` . Prove it that way rather than by the
chapter's dyadic telescoping, and say so. -/
theorem psi_isBigO : (fun x : ℝ => psi x) =O[atTop] (fun x : ℝ => x) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [ElementaryPNT.psi_eq_chebyshevPsi, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg x), abs_of_nonneg hx]
  exact Chebyshev.psi_le_const_mul_self hx

/-- (chapter step S1.6). `∑_{n ≤ x} Λ(n)/n = log x + O(1)`.

Chapter route: from `log⌊x⌋! = ∑_{n ≤ x} Λ(n)⌊x/n⌋` (the identity an earlier stage already used, in
`Real/Round8Aux.lean`) and `log⌊x⌋! = x log x − x + O(log x)`, replace `⌊x/n⌋` by `x/n` at a
cost of `∑_{n ≤ x} Λ(n) = ψ(x) = O(x)` by R9-4, then divide by `x`. The constant `2` in the
statement is a convenience: if the argument gives a different explicit constant,  -/
theorem mertens : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n) - Real.log x| ≤ C := by
  refine ⟨9, by norm_num, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 := abs_mul_sum_vonMangoldt_div_sub_log_factorial_le hx
  have h2 := abs_log_factorial_floor_sub_le hx
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9
    linarith
  have hcomb : |x * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n)
      - Real.log x)| ≤ 9 * x := by
    have hsplit : x * ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n)
        - Real.log x)
        = (x * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n)
            - Real.log ((⌊x⌋₊).factorial))
          + (Real.log ((⌊x⌋₊).factorial) - x * Real.log x) := by ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    nlinarith [h1, h2]
  rw [abs_mul, abs_of_pos hx0] at hcomb
  have : |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n) - Real.log x| * x
      ≤ 9 * x := by linarith [hcomb]
  exact le_of_mul_le_mul_right (by linarith) hx0

/-! ## Stage 2: the Tatuzawa–Iseki identity -/

/-- (chapter step S2.1).
`F(x) log x + ∑_{n ≤ x} F(x/n) Λ(n) = ∑_{k ≤ x} μ(k) log(x/k) ∑_{j ≤ x/k} F(x/(kj))`.

Chapter proof: with `(M F)(x) = ∑_{k ≤ x} F(x/k)` and `(L F)(x) = log x · F(x)`,
`(LM − ML)F (x) = ∑_{k ≤ x} log(k) F(x/k)`; applying `M⁻¹` (Möbius inversion) gives
`(M⁻¹ L M − L) F (x) = ∑_{j,k ≤ x} μ(j) log(k) F(x/(jk)) = ∑_{n ≤ x} F(x/n) ∑_{j ∣ n} μ(j) log(n/j)`,
and `∑_{j ∣ n} μ(j) log(n/j) = Λ(n)` is Mathlib's
`ArithmeticFunction.moebius_mul_log_eq_vonMangoldt`. The work in Lean is the double-sum
reindexing over pairs `(j,k)` with `jk ≤ x`. -/
theorem tatuzawa_iseki (F : ℝ → ℝ) (x : ℝ) (hx : 1 ≤ x) :
    F x * Real.log x + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F (x / n) * ArithmeticFunction.vonMangoldt n =
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) *
        ∑ j ∈ Finset.Icc 1 ⌊x / k⌋₊, F (x / (k * j)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set m := ⌊x⌋₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.one_le_floor_iff]; exact hx
  -- the right-hand side as a double sum with natural-number division
  have hR : ∑ k ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) *
        ∑ j ∈ Finset.Icc 1 ⌊x / (k : ℝ)⌋₊, F (x / (k * j))
      = ∑ k ∈ Finset.Icc 1 m, ∑ j ∈ Finset.Icc 1 (m / k),
          (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) * F (x / (k * j)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ⌊x / (k : ℝ)⌋₊ = m / k by rw [Nat.floor_div_natCast, hm], Finset.mul_sum]
  rw [hR, sum_Icc_sum_Icc_div_eq_sum_divisors]
  -- the inner sum over the divisors of `n`
  have hinner : ∀ n ∈ Finset.Icc 1 m,
      (∑ k ∈ n.divisors, (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) *
          F (x / (k * ((n / k : ℕ) : ℝ))))
        = F (x / n) * (Real.log x * (if n = 1 then 1 else 0)
            + ArithmeticFunction.vonMangoldt n) := by
    intro n _
    have hterm : ∀ k ∈ n.divisors,
        (ArithmeticFunction.moebius k : ℝ) * Real.log (x / k) * F (x / (k * ((n / k : ℕ) : ℝ)))
          = F (x / n) * ((ArithmeticFunction.moebius k : ℝ) * Real.log (x / k)) := by
      intro k hk
      have hdvd : k ∣ n := (Nat.mem_divisors.1 hk).1
      have hcast : (k : ℝ) * ((n / k : ℕ) : ℝ) = (n : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hcast]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      sum_divisors_moebius_mul_log_div hx0 n]
  rw [Finset.sum_congr rfl hinner]
  -- split off the term `n = 1`
  have hsplit : ∀ n ∈ Finset.Icc 1 m,
      F (x / n) * (Real.log x * (if n = 1 then 1 else 0) + ArithmeticFunction.vonMangoldt n)
        = (if n = 1 then F (x / n) * Real.log x else 0)
          + F (x / n) * ArithmeticFunction.vonMangoldt n := by
    intro n _
    split_ifs with h <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.Icc 1 m) 1 (fun n : ℕ => F (x / n) * Real.log x)]
  simp [hm1]

end SelbergPNT
