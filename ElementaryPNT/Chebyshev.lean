/-
ElementaryPNT.Chebyshev — the identity `log m! = ∑_{d ≤ m} Λ(d)⌊m/d⌋`, the Chebyshev lower
bound built from it, and the identification of this development's `psi` with Mathlib's
`Chebyshev.psi`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs

open Filter Topology Asymptotics Finset ArithmeticFunction

namespace ElementaryPNT

/-! ## The Λ-form of `log (m!)` -/

/-- `log (m!) = ∑_{d ≤ m} Λ(d) ⌊m/d⌋`: sum the identity `∑_{d ∣ k} Λ(d) = log k` over `k ≤ m`
and count, for each `d`, the multiples of `d` up to `m`. -/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (m : ℕ) :
    Real.log (m.factorial) = ∑ d ∈ Finset.Ioc 0 m, vonMangoldt d * ((m / d : ℕ) : ℝ) := by
  have hlog : Real.log (m.factorial) = ∑ k ∈ Finset.Ioc 0 m, Real.log k := by
    rw [← Finset.prod_Ico_id_eq_factorial m, Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr
      · ext k; simp; omega
      · intro k _; rfl
    · intro k hk
      simp only [mem_Ico] at hk
      have : (0:ℝ) < k := by exact_mod_cast hk.1
      positivity
  rw [hlog]
  have step1 : ∑ k ∈ Finset.Ioc 0 m, Real.log k
      = ∑ k ∈ Finset.Ioc 0 m, ∑ d ∈ k.divisors, vonMangoldt d :=
    Finset.sum_congr rfl fun k _ => vonMangoldt_sum.symm
  rw [step1,
    Finset.sum_comm' (t' := Finset.Ioc 0 m) (s' := fun d => (Finset.Ioc 0 m).filter (d ∣ ·))]
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
theorem two_mul_div_le_two_mul_div_add_one (n d : ℕ) (hd : 0 < d) :
    (2 * n) / d ≤ 2 * (n / d) + 1 := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.div_add_mod (2 * n) d
  have h3 : n % d < d := Nat.mod_lt _ hd
  have h4 : (2 * n) % d < d := Nat.mod_lt _ hd
  have e : d * (2 * (n / d) + 2) = 2 * (d * (n / d)) + 2 * d := by ring
  have hlt : d * (2 * n / d) < d * (2 * (n / d) + 2) := by
    rw [e]
    set X := d * (2 * n / d)
    set Y := d * (n / d)
    set a := (2 * n) % d
    set b := n % d
    omega
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-! ## Chebyshev's lower bound -/

/-- `log C(2n, n) ≤ ψ(2n)`, the arithmetic heart of Chebyshev's lower bound. -/
theorem log_centralBinom_le_psi (n : ℕ) :
    Real.log (Nat.centralBinom n) ≤ Chebyshev.psi ((2 * n : ℕ) : ℝ) := by
  have hfac : (Nat.centralBinom n : ℝ) * (n.factorial) * (n.factorial)
      = ((2 * n).factorial : ℕ) := by
    rw [Nat.centralBinom]
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  have hpos : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hCB : (0:ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
  have hsplit : Real.log (Nat.centralBinom n)
      = Real.log ((2 * n).factorial) - 2 * Real.log (n.factorial) := by
    have h := congrArg Real.log hfac
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at h
    linarith [h]
  rw [hsplit, log_factorial_eq_sum_vonMangoldt_mul_div, log_factorial_eq_sum_vonMangoldt_mul_div]
  have hext : ∑ d ∈ Finset.Ioc 0 n, vonMangoldt d * ((n / d : ℕ) : ℝ)
      = ∑ d ∈ Finset.Ioc 0 (2 * n), vonMangoldt d * ((n / d : ℕ) : ℝ) := by
    apply Finset.sum_subset
    · intro d hd; simp only [mem_Ioc] at *; omega
    · intro d hd hnd
      simp only [mem_Ioc] at hd hnd
      have : n / d = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]
  rw [hext, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hpsi : Chebyshev.psi ((2 * n : ℕ) : ℝ) = ∑ d ∈ Finset.Ioc 0 (2 * n), vonMangoldt d := by
    rw [Chebyshev.psi, Nat.floor_natCast]
  rw [hpsi]
  refine Finset.sum_le_sum fun d hd => ?_
  simp only [mem_Ioc] at hd
  have hΛ : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
  have hco : (((2 * n) / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ) ≤ 1 := by
    have : (((2 * n) / d : ℕ) : ℝ) ≤ 2 * ((n / d : ℕ) : ℝ) + 1 := by
      exact_mod_cast two_mul_div_le_two_mul_div_add_one n d hd.1
    linarith
  nlinarith [hΛ]

/-- `ψ(2n) ≥ n log 4 − log (2n)` for `n ≥ 1`. -/
theorem chebyshev_psi_lower_nat {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n) ≤ Chebyshev.psi (2 * (n : ℝ)) := by
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h4 : (4 : ℕ) ^ n ≤ 2 * n * Nat.centralBinom n :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hCB : (0:ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
  have h2n : (0:ℝ) < 2 * n := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog : Real.log ((4:ℝ) ^ n) ≤ Real.log ((2 * n : ℝ) * Nat.centralBinom n) := by
    apply Real.log_le_log (by positivity)
    have : ((4 ^ n : ℕ) : ℝ) ≤ ((2 * n * Nat.centralBinom n : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at this
    linarith
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at hlog
  have hb := log_centralBinom_le_psi n
  rw [hcast] at hb
  linarith

/-- **Chebyshev's lower bound**, in the explicit form `x/2 ≤ ψ(x)` for all large `x`. -/
theorem chebyshev_psi_lower_real : ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.psi x := by
  have hbound := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 0.05 by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ), hbound] with x hx hlogx
  have hx0 : (0:ℝ) < x := by linarith
  have hlog : Real.log x ≤ 0.05 * x := by
    simp only [Real.norm_eq_abs, id_eq, abs_of_pos hx0] at hlogx
    calc Real.log x ≤ |Real.log x| := le_abs_self _
      _ ≤ 0.05 * x := hlogx
  set n := ⌊x / 2⌋₊ with hn
  have hn1 : 1 ≤ n := by
    rw [hn, Nat.one_le_floor_iff]
    linarith
  have hnle : 2 * (n : ℝ) ≤ x := by
    have := Nat.floor_le (show (0:ℝ) ≤ x / 2 by linarith)
    rw [← hn] at this
    linarith
  have hngt : x / 2 - 1 < (n : ℝ) := by
    have := Nat.lt_floor_add_one (x / 2)
    rw [← hn] at this
    linarith
  have hmono : Chebyshev.psi (2 * (n : ℝ)) ≤ Chebyshev.psi x := Chebyshev.psi_mono hnle
  have hkey := chebyshev_psi_lower_nat hn1
  have hlog4 : (1.386 : ℝ) ≤ Real.log 4 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlog2n : Real.log (2 * (n : ℝ)) ≤ Real.log x := by
    apply Real.log_le_log _ hnle
    have : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hkey, hmono, hlog2n, hlog, hngt, hlog4]

/-! ## Consequences for `θ` and `π` -/

/-- `2 √x log x = o(x)`, the error term in `|ψ − θ| ≤ 2 √x log x`. -/
theorem sqrt_mul_log_isLittleO :
    (fun x : ℝ => 2 * Real.sqrt x * Real.log x) =o[atTop] (fun x : ℝ => x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ ((1:ℝ) / 2)) :=
    _root_.isLittleO_log_rpow_atTop (by norm_num)
  have h2 : (fun x : ℝ => 2 * Real.sqrt x) =O[atTop] (fun x : ℝ => x ^ ((1:ℝ) / 2)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [Real.sqrt_eq_rpow]
    simp [abs_of_nonneg, Real.rpow_nonneg hx]
  refine (h2.mul_isLittleO h1).congr' (by filter_upwards with x using by ring) ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hx]

/-- Chebyshev's lower bound for `θ`: `x/4 ≤ θ(x)` for all large `x`. -/
theorem chebyshev_theta_lower_real : ∀ᶠ x : ℝ in atTop, x / 4 ≤ Chebyshev.theta x := by
  have herr := sqrt_mul_log_isLittleO.bound (show (0:ℝ) < 1 / 4 by norm_num)
  filter_upwards [chebyshev_psi_lower_real, herr, eventually_ge_atTop (1:ℝ)] with x hx herrx hx1
  have hx0 : (0:ℝ) < x := by linarith
  have hsmall : 2 * Real.sqrt x * Real.log x ≤ x / 4 := by
    simp only [Real.norm_eq_abs, abs_of_pos hx0] at herrx
    calc 2 * Real.sqrt x * Real.log x ≤ |2 * Real.sqrt x * Real.log x| := le_abs_self _
      _ ≤ 1 / 4 * x := herrx
      _ = x / 4 := by ring
  have hdiff : |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x :=
    Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have := abs_le.mp hdiff
  linarith [this.1, this.2]

/-- The elementary bound `θ(x) ≤ π(x) · log x`, with `π(x)` written as the number of primes in
`Ioc 0 ⌊x⌋₊`. -/
theorem theta_le_card_primes_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.theta x ≤ (((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) * Real.log x := by
  rw [Chebyshev.theta]
  calc ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p
      ≤ ∑ _p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log x := by
        refine Finset.sum_le_sum fun p hp => ?_
        simp only [mem_filter, mem_Ioc] at hp
        have hp0 : (0:ℝ) < p := by exact_mod_cast hp.1.1
        refine Real.log_le_log hp0 ?_
        calc (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hp.1.2
          _ ≤ x := Nat.floor_le (by linarith)
    _ = (((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The blueprint's `ψ` is Mathlib's. -/
theorem psi_eq_chebyshevPsi (x : ℝ) : SelbergPNT.psi x = Chebyshev.psi x := by
  rw [SelbergPNT.psi, Chebyshev.psi]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [mem_Icc, mem_Ioc]
  omega

end ElementaryPNT
