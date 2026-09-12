/-
Copyright (c) 2026 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chebyshev's lower bound

This file proves Chebyshev's lower bound for the Chebyshev function `ψ`, the one item left on the
TODO list of `Mathlib/NumberTheory/Chebyshev.lean`, which so far has only the upper bounds
`Chebyshev.theta_le_log4_mul_x` and `Chebyshev.psi_le_const_mul_self`.

## Main results

* `Chebyshev.mul_log_two_sub_le_psi`: the explicit inequality
  `x * log 2 - log x - log 4 ≤ ψ x` for `1 ≤ x`;
* `Chebyshev.eventually_mul_le_psi`: consequently `c * x ≤ ψ x` for all large `x`, for every
  constant `c < log 2`;
* `Chebyshev.isBigO_id_psi`: `x = O(ψ x)`, the qualitative form of Chebyshev's lower bound.

## Proof idea

Summing the von Mangoldt identity `∑_{d ∣ k} Λ d = log k` over `k ≤ m` and counting, for each `d`,
the multiples of `d` up to `m`, gives
`log (m !) = ∑_{d ≤ m} Λ d * ⌊m / d⌋` (`Chebyshev.log_factorial_eq_sum_vonMangoldt_mul_div`).
Applying this to `m = 2n` and to `m = n` and subtracting,
`log (2n).centralBinom = ∑_{d ≤ 2n} Λ d * (⌊2n/d⌋ - 2⌊n/d⌋) ≤ ∑_{d ≤ 2n} Λ d = ψ (2n)`,
because `⌊2n/d⌋ - 2⌊n/d⌋ ∈ {0, 1}`. Since `4 ^ n ≤ 2n * n.centralBinom`
(`Nat.four_pow_le_two_mul_self_mul_centralBinom`), this gives `n log 4 - log (2n) ≤ ψ (2n)`, and
passing from `2n` to a real `x` by monotonicity of `ψ` yields the main inequality.

This is the classical central binomial coefficient argument, with the bookkeeping over prime powers
replaced by the von Mangoldt identity, which shortens it considerably.

## Sharpness

The constant obtained here is `log 2 = 0.693…`, and it is the best the argument gives as it stands:
the input `4 ^ n ≤ 2n * n.centralBinom` is sharp up to the polynomial factor, so the method cannot
give more than `log 4` per `2n`, i.e. `log 2` per unit. Chebyshev's own refinement, which uses
`(30n)! n! / ((15n)! (10n)! (6n)!)` in place of the central binomial coefficient, gives the larger
constant `log (2^{1/2} 3^{1/3} 5^{1/5} / 30^{1/30}) = 0.921…` at the cost of the corresponding
factorial bookkeeping; the truth is `1`, by the prime number theorem.
-/

open Filter Finset ArithmeticFunction Asymptotics
open scoped Nat

namespace Chebyshev

/-- `log (m !) = ∑_{d ≤ m} Λ d * ⌊m / d⌋`: sum `∑_{d ∣ k} Λ d = log k` over `k ≤ m` and count,
for each `d`, the multiples of `d` up to `m`. -/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (m : ℕ) :
    Real.log (m !) = ∑ d ∈ Ioc 0 m, Λ d * ((m / d : ℕ) : ℝ) := by
  have hlog : Real.log (m !) = ∑ k ∈ Ioc 0 m, Real.log k := by
    rw [← Finset.prod_Ico_id_eq_factorial m, Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr
      · ext k; simp; omega
      · intro k _; rfl
    · intro k hk
      simp only [mem_Ico] at hk
      have : (0 : ℝ) < k := by exact_mod_cast hk.1
      positivity
  rw [hlog]
  have step : ∑ k ∈ Ioc 0 m, Real.log k = ∑ k ∈ Ioc 0 m, ∑ d ∈ k.divisors, Λ d :=
    Finset.sum_congr rfl fun k _ => vonMangoldt_sum.symm
  rw [step, Finset.sum_comm' (t' := Ioc 0 m) (s' := fun d => {k ∈ Ioc 0 m | d ∣ k})]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro k d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hk0, hkm⟩, hdk, hk⟩
      exact ⟨⟨⟨hk0, hkm⟩, hdk⟩,
        ⟨Nat.pos_of_dvd_of_pos hdk hk0, le_trans (Nat.le_of_dvd hk0 hdk) hkm⟩⟩
    · rintro ⟨⟨⟨hk0, hkm⟩, hdk⟩, -⟩
      exact ⟨⟨hk0, hkm⟩, hdk, by omega⟩

/-- `⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1`. -/
theorem two_mul_div_le_two_mul_div_add_one (n : ℕ) {d : ℕ} (hd : 0 < d) :
    2 * n / d ≤ 2 * (n / d) + 1 := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.div_add_mod (2 * n) d
  have h3 : n % d < d := Nat.mod_lt _ hd
  have h4 : 2 * n % d < d := Nat.mod_lt _ hd
  have e : d * (2 * (n / d) + 2) = 2 * (d * (n / d)) + 2 * d := by ring
  have hlt : d * (2 * n / d) < d * (2 * (n / d) + 2) := by
    rw [e]
    set X := d * (2 * n / d)
    set Y := d * (n / d)
    set a := 2 * n % d
    set b := n % d
    omega
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-- `log (n.centralBinom) ≤ ψ (2n)`, the arithmetic heart of Chebyshev's lower bound. -/
theorem log_centralBinom_le_psi (n : ℕ) :
    Real.log (n.centralBinom) ≤ ψ ((2 * n : ℕ) : ℝ) := by
  have hfac : (n.centralBinom : ℝ) * (n !) * (n !) = ((2 * n)! : ℕ) := by
    rw [Nat.centralBinom]
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  have hpos : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hCB : (0 : ℝ) < n.centralBinom := by exact_mod_cast Nat.centralBinom_pos n
  have hsplit : Real.log (n.centralBinom) = Real.log ((2 * n)!) - 2 * Real.log (n !) := by
    have h := congrArg Real.log hfac
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at h
    linarith [h]
  rw [hsplit, log_factorial_eq_sum_vonMangoldt_mul_div, log_factorial_eq_sum_vonMangoldt_mul_div]
  have hext : ∑ d ∈ Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ)
      = ∑ d ∈ Ioc 0 (2 * n), Λ d * ((n / d : ℕ) : ℝ) := by
    apply Finset.sum_subset
    · intro d hd; simp only [mem_Ioc] at *; omega
    · intro d hd hnd
      simp only [mem_Ioc] at hd hnd
      have : n / d = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]
  rw [hext, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hpsi : ψ ((2 * n : ℕ) : ℝ) = ∑ d ∈ Ioc 0 (2 * n), Λ d := by
    rw [psi, Nat.floor_natCast]
  rw [hpsi]
  refine Finset.sum_le_sum fun d hd => ?_
  simp only [mem_Ioc] at hd
  have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
  have hco : ((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ) ≤ 1 := by
    have : ((2 * n / d : ℕ) : ℝ) ≤ 2 * ((n / d : ℕ) : ℝ) + 1 := by
      exact_mod_cast two_mul_div_le_two_mul_div_add_one n hd.1
    linarith
  nlinarith [hΛ]

/-- `n log 4 - log (2n) ≤ ψ (2n)` for `1 ≤ n`. -/
theorem psi_two_mul_nat_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n) ≤ ψ (2 * (n : ℝ)) := by
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h4 : 4 ^ n ≤ 2 * n * n.centralBinom := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hCB : (0 : ℝ) < n.centralBinom := by exact_mod_cast Nat.centralBinom_pos n
  have h2n : (0 : ℝ) < 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog : Real.log ((4 : ℝ) ^ n) ≤ Real.log ((2 * n : ℝ) * n.centralBinom) := by
    apply Real.log_le_log (by positivity)
    have : ((4 ^ n : ℕ) : ℝ) ≤ ((2 * n * n.centralBinom : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at this
    linarith
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at hlog
  have hb := log_centralBinom_le_psi n
  rw [hcast] at hb
  linarith

/-- **Chebyshev's lower bound**, in explicit form: `x log 2 - log x - log 4 ≤ ψ x` for `1 ≤ x`. -/
theorem mul_log_two_sub_le_psi {x : ℝ} (hx : 1 ≤ x) :
    x * Real.log 2 - Real.log x - Real.log 4 ≤ ψ x := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases lt_or_ge x 2 with hx2 | hx2
  · have : ψ x = 0 := psi_eq_zero_of_lt_two hx2
    rw [this]
    nlinarith
  set n := ⌊x / 2⌋₊ with hn
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_floor_iff]
    linarith
  have hnle : 2 * (n : ℝ) ≤ x := by
    have := Nat.floor_le (show (0 : ℝ) ≤ x / 2 by linarith)
    rw [← hn] at this
    linarith
  have hngt : x / 2 - 1 < (n : ℝ) := by
    have := Nat.lt_floor_add_one (x / 2)
    rw [← hn] at this
    linarith
  have hmono : ψ (2 * (n : ℝ)) ≤ ψ x := psi_mono hnle
  have hkey := psi_two_mul_nat_lower hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog2n : Real.log (2 * (n : ℝ)) ≤ Real.log x := Real.log_le_log (by linarith) hnle
  nlinarith

/-- Chebyshev's lower bound: for every `c < log 2`, `c x ≤ ψ x` for all large `x`. -/
theorem eventually_mul_le_psi {c : ℝ} (hc : c < Real.log 2) :
    ∀ᶠ x : ℝ in atTop, c * x ≤ ψ x := by
  have hpos : 0 < Real.log 2 - c := by linarith
  have hbound := Real.isLittleO_log_id_atTop.bound (show 0 < (Real.log 2 - c) / 2 by linarith)
  have hthr : ∀ᶠ x : ℝ in atTop, 2 * Real.log 4 / (Real.log 2 - c) ≤ x :=
    eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℝ), hbound, hthr] with x hx hlogx hxthr
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log x ≤ (Real.log 2 - c) / 2 * x := by
    simp only [Real.norm_eq_abs, id_eq, abs_of_pos hx0] at hlogx
    exact le_trans (le_abs_self _) hlogx
  have hkey := mul_log_two_sub_le_psi hx
  have hlog4 : Real.log 4 ≤ (Real.log 2 - c) / 2 * x := by
    rw [div_le_iff₀ hpos] at hxthr
    linarith
  linarith

/-- Chebyshev's lower bound in asymptotic form: `x = O(ψ x)`. -/
theorem isBigO_id_psi : (fun x : ℝ => x) =O[atTop] fun x : ℝ => ψ x := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [eventually_mul_le_psi (show Real.log 2 / 2 < Real.log 2 by linarith),
    eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0, abs_of_nonneg (psi_nonneg x)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  linarith

end Chebyshev
