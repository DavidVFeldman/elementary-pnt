/-
ElementaryPNT.Stage4cStep1 — auxiliary development for `ElementaryPNT.Stage4c`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage3
import ElementaryPNT.Stage4a
import ElementaryPNT.Stage4bAux
import ElementaryPNT.Stage4bGap
import ElementaryPNT.Stage4cAux

open Filter Topology MeasureTheory

namespace SelbergPNT

namespace Stage4cStep1

/-! ## The two fundamental-theorem evaluations -/

/-- `∫₂^y ((R x / x) log x + S x / x) dx = S y log y`: the integration by parts, in the form of
the fundamental theorem of calculus for the right derivative of `x ↦ S(x) log x`. -/
theorem integral_S_log (y : ℝ) (hy : 2 ≤ y) :
    (∫ x in (2:ℝ)..y, ((R x / x) * Real.log x + S x / x)) = S y * Real.log y := by
  have hIcc : Set.Icc (2 : ℝ) y ⊆ Set.Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le (by norm_num) hu.1
  have hcont : ContinuousOn (fun u : ℝ => S u * Real.log u) (Set.Icc 2 y) := by
    refine (Stage4bAux.continuousOn_S.mono hIcc).mul ?_
    exact Real.continuousOn_log.mono (fun u hu => ne_of_gt (hIcc hu))
  have hderiv : ∀ x ∈ Set.Ioo (2:ℝ) y,
      HasDerivWithinAt (fun u : ℝ => S u * Real.log u) ((R x / x) * Real.log x + S x / x)
        (Set.Ioi x) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    have h1 := Stage4bAux.hasDerivWithinAt_S hx0
    have h2 : HasDerivWithinAt Real.log (1 / x) (Set.Ioi x) x := by
      simpa [one_div] using (Real.hasDerivAt_log (ne_of_gt hx0)).hasDerivWithinAt
    have h3 := h1.mul h2
    convert h3 using 1
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => (R x / x) * Real.log x + S x / x) volume 2 y := by
    refine IntervalIntegrable.add ?_ ?_
    · exact (Stage5Aux.intervalIntegrable_R_div (by norm_num) (by linarith)).mul_continuousOn
        (Real.continuousOn_log.mono (by
          rw [Set.uIcc_of_le hy]; exact fun u hu => ne_of_gt (hIcc hu)))
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hy]
      exact (Stage4bAux.continuousOn_S.mono hIcc).div (by fun_prop)
        fun u hu => ne_of_gt (hIcc hu)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hy hcont hderiv hint
  rw [hmain, Stage4bAux.S_two]
  ring

/-- `u ↦ S(u/n)` has the right derivative `R(x/n)/x` at every `x > 0`. -/
theorem hasDerivWithinAt_S_comp (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (fun u : ℝ => S (u / n)) (R (x / n) / x) (Set.Ioi x) x := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hxn : (0:ℝ) < x / n := by positivity
  have hg : HasDerivWithinAt (fun u : ℝ => u / n) (1 / n) (Set.Ioi x) x := by
    simpa using ((hasDerivAt_id x).div_const (n : ℝ)).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun u : ℝ => u / n) (Set.Ioi x) (Set.Ioi (x / n)) := by
    intro u hu
    simp only [Set.mem_Ioi] at hu ⊢
    gcongr
  have hcomp := (Stage4bAux.hasDerivWithinAt_S hxn).comp x hg hmaps
  have heq : R (x / n) / (x / n) * (1 / n) = R (x / n) / x := by field_simp
  rw [heq] at hcomp
  exact hcomp

/-- `u ↦ S(u/n)` is continuous away from the origin. -/
theorem continuousOn_S_comp (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => S (u / n)) (Set.Icc a b) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  refine Stage4bAux.continuousOn_S.comp (by fun_prop) ?_
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
  simp only [Set.mem_Ioi]
  positivity

/-- `x ↦ R(x/n)/x` is interval integrable away from the origin. -/
theorem intervalIntegrable_R_div_comp (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => R (x / n) / x) volume a b := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ u : ℝ, u ∈ Set.uIcc a b → u ≠ 0 := by
    intro u hu
    refine ne_of_gt (lt_of_lt_of_le (lt_min ha hb) ?_)
    rw [Set.uIcc_eq_union] at hu
    rcases hu with hu | hu
    · exact le_trans (min_le_left a b) hu.1
    · exact le_trans (min_le_right a b) hu.1
  have h1 : IntervalIntegrable (fun u : ℝ => psi (u / n)) volume a b := by
    refine MonotoneOn.intervalIntegrable ?_
    intro u _ v _ huv
    exact Stage5Aux.psi_mono (by gcongr)
  have h2 : IntervalIntegrable (fun u : ℝ => psi (u / n) * (1 / u)) volume a b :=
    h1.mul_continuousOn (ContinuousOn.div continuousOn_const (by fun_prop) hpos)
  have h3 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / n) volume a b := intervalIntegrable_const
  refine IntervalIntegrable.congr (f := fun u : ℝ => psi (u / n) * (1 / u) - 1 / n) ?_ (h2.sub h3)
  intro u hu
  have hu0 : u ≠ 0 := hpos u (Set.uIoc_subset_uIcc hu)
  simp only [R]
  field_simp

/-- The second evaluation: `∫_a^b R(x/n)/x dx = S(b/n) − S(a/n)`. -/
theorem integral_R_div_comp (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, R (x / n) / x) = S (b / n) - S (a / n) := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (continuousOn_S_comp n hn ha) (fun x hx => hasDerivWithinAt_S_comp n hn (lt_trans ha hx.1))
    (intervalIntegrable_R_div_comp n hn ha (lt_of_lt_of_le ha hab))

/-! ## The terms of the sum, cut off below `x = n` -/

/-- The `n`-th term of the integrand, which vanishes for `x < n`. -/
noncomputable def term (n : ℕ) (x : ℝ) : ℝ :=
  if (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n * (R (x / n) / x) else 0

theorem term_ae_zero (n : ℕ) :
    (fun _ : ℝ => (0 : ℝ)) =ᵐ[volume.restrict (Set.uIoc 2 (max 2 (n : ℝ)))] term n := by
  have hae : ∀ᵐ u : ℝ, u ≠ max 2 (n : ℝ) := by rw [ae_iff]; simp
  filter_upwards [self_mem_ae_restrict measurableSet_uIoc, ae_restrict_of_ae hae] with u hmem hu
  rw [Set.uIoc_of_le (le_max_left _ _)] at hmem
  have h1 : u < max 2 (n : ℝ) := lt_of_le_of_ne hmem.2 hu
  have h2 : (2 : ℝ) < u := hmem.1
  have hlt : u < (n : ℝ) := by
    rcases max_cases (2 : ℝ) (n : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h1; linarith
    · rw [he] at h1; exact h1
  simp [term, not_le.2 hlt]

theorem intervalIntegrable_term_lower (n : ℕ) :
    IntervalIntegrable (term n) volume 2 (max 2 (n : ℝ)) := by
  rw [intervalIntegrable_iff]
  exact (integrable_zero ℝ ℝ _).congr (term_ae_zero n)

theorem intervalIntegrable_term_upper (n : ℕ) (hn : 1 ≤ n) {y : ℝ} (hy : 2 ≤ y)
    (hny : (n : ℝ) ≤ y) :
    IntervalIntegrable (term n) volume (max 2 (n : ℝ)) y := by
  have hcy : max 2 (n : ℝ) ≤ y := max_le hy hny
  have hc0 : (0 : ℝ) < max 2 (n : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine IntervalIntegrable.congr
    (f := fun x : ℝ => ArithmeticFunction.vonMangoldt n * (R (x / n) / x)) ?_
    (((intervalIntegrable_R_div_comp n hn hc0 (lt_of_lt_of_le hc0 hcy))).const_mul _)
  intro u hu
  rw [Set.uIoc_of_le hcy] at hu
  have : (n : ℝ) ≤ u := le_trans (le_max_right _ _) hu.1.le
  simp [term, this]

theorem intervalIntegrable_term (n : ℕ) (hn : 1 ≤ n) {y : ℝ} (hy : 2 ≤ y) (hny : (n : ℝ) ≤ y) :
    IntervalIntegrable (term n) volume 2 y :=
  (intervalIntegrable_term_lower n).trans (intervalIntegrable_term_upper n hn hy hny)

theorem integral_term (n : ℕ) (hn : 1 ≤ n) {y : ℝ} (hy : 2 ≤ y) (hny : (n : ℝ) ≤ y) :
    (∫ x in (2:ℝ)..y, term n x)
      = ArithmeticFunction.vonMangoldt n * (S (y / n) - S (max 2 (n : ℝ) / n)) := by
  have hcy : max 2 (n : ℝ) ≤ y := max_le hy hny
  have hc0 : (0 : ℝ) < max 2 (n : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_term_lower n) (intervalIntegrable_term_upper n hn hy hny)
  have hlow : (∫ x in (2:ℝ)..(max 2 (n : ℝ)), term n x) = 0 := by
    have hzero : (∫ x in (2:ℝ)..(max 2 (n : ℝ)), term n x)
        = ∫ _x in (2:ℝ)..(max 2 (n : ℝ)), (0 : ℝ) := by
      rw [intervalIntegral.integral_of_le (le_max_left _ _),
        intervalIntegral.integral_of_le (le_max_left _ _)]
      refine MeasureTheory.integral_congr_ae ?_
      have h := term_ae_zero n
      rw [Set.uIoc_of_le (le_max_left (2:ℝ) (n:ℝ))] at h
      exact h.symm
    rw [hzero]; simp
  have hup : (∫ x in (max 2 (n : ℝ))..y, term n x)
      = ArithmeticFunction.vonMangoldt n * (S (y / n) - S (max 2 (n : ℝ) / n)) := by
    have hcongr : (∫ x in (max 2 (n : ℝ))..y, term n x)
        = ∫ x in (max 2 (n : ℝ))..y, ArithmeticFunction.vonMangoldt n * (R (x / n) / x) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hcy] at hu
      have : (n : ℝ) ≤ u := le_trans (le_max_right _ _) hu.1
      simp [term, this]
    rw [hcongr, intervalIntegral.integral_const_mul, integral_R_div_comp n hn hc0 hcy]
  rw [← hsplit, hlow, hup, zero_add]

/-- On `[2, y]` the integrand `(1/x) ∑_{n ≤ x} R(x/n) Λ(n)` is the sum over `n ≤ y` of the
cut-off terms. -/
theorem sum_term_eq {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, term n x)
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x := by
  classical
  have hfilter : (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x) = Finset.Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_floor_iff hx).2 h2⟩
    · rintro ⟨h1, h2⟩
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).1 h2
      exact ⟨⟨h1, Nat.le_floor ((Nat.le_floor_iff hx).1 h2 |>.trans hxy)⟩, hnx⟩
  calc (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, term n x)
      = ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ x),
          ArithmeticFunction.vonMangoldt n * (R (x / n) / x) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun n _ => rfl
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (R (x / n) / x) := by
        rw [hfilter]
    _ = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun n _ => by ring

/-! ## -/

/-- The first integrand is interval integrable on `[2, y]`. -/
theorem intervalIntegrable_F {y : ℝ} (hy : 2 ≤ y) :
    IntervalIntegrable (fun x : ℝ => (R x / x) * Real.log x + S x / x) volume 2 y := by
  have hIcc : Set.Icc (2 : ℝ) y ⊆ Set.Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le (by norm_num) hu.1
  refine IntervalIntegrable.add ?_ ?_
  · exact (Stage5Aux.intervalIntegrable_R_div (by norm_num) (by linarith)).mul_continuousOn
      (Real.continuousOn_log.mono (by
        rw [Set.uIcc_of_le hy]; exact fun u hu => ne_of_gt (hIcc hu)))
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hy]
    exact (Stage4bAux.continuousOn_S.mono hIcc).div (by fun_prop) fun u hu => ne_of_gt (hIcc hu)

/-- (chapter step S4.1a), with the range extended to `y ≥ 1`: there is `C₁ > 0` with

  `|S(y) log y + ∑_{n ≤ y} S(y/n) Λ(n)| ≤ C₁ y`. -/
theorem selberg_S_form : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ y : ℝ, 1 ≤ y →
    |S y * Real.log y + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, S (y / n) * ArithmeticFunction.vonMangoldt n|
      ≤ C₁ * y := by
  obtain ⟨C₀, hC₀, hsel⟩ := Stage4cAux.selberg_first_const
  refine ⟨C₀ + 6, by linarith, fun y hy => ?_⟩
  rcases lt_or_ge y 2 with hy2 | hy2
  · -- below `2` the sum has only the term `n = 1`, where `Λ(1) = 0`
    have hfloor : ⌊y⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by exact_mod_cast hy, by push_cast; linarith⟩
    have hS : S y = 2 - y := Stage4cAux.S_eq_two_sub (by linarith) (by linarith)
    have hlog : Real.log y ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    rw [hfloor]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one,
      ArithmeticFunction.vonMangoldt_apply_one, mul_zero, add_zero]
    rw [hS, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hy0 : (0:ℝ) < y := by linarith
    set M := ⌊y⌋₊ with hM
    have hMy : ∀ n ∈ Finset.Icc 1 M, (n : ℝ) ≤ y := by
      intro n hn
      simp only [Finset.mem_Icc, hM] at hn
      exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le (le_of_lt hy0))
    have hEq : Set.EqOn (fun x : ℝ => ∑ n ∈ Finset.Icc 1 M, term n x)
        (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x)
        (Set.uIcc 2 y) := by
      intro u hu
      rw [Set.uIcc_of_le hy2] at hu
      exact sum_term_eq (le_trans (by norm_num) hu.1) hu.2
    have hsumint : IntervalIntegrable (fun x : ℝ => ∑ n ∈ Finset.Icc 1 M, term n x) volume 2 y := by
      have h := IntervalIntegrable.sum (μ := volume) (a := 2) (b := y) (Finset.Icc 1 M)
        (f := fun n => term n) (fun n hn =>
          intervalIntegrable_term n (Finset.mem_Icc.1 hn).1 hy2 (hMy n hn))
      exact h.congr (fun u _ => by simp [Finset.sum_apply])
    have hGint : IntervalIntegrable
        (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          R (x / n) * ArithmeticFunction.vonMangoldt n) / x) volume 2 y :=
      IntervalIntegrable.congr (hEq.mono Set.uIoc_subset_uIcc) hsumint
    have hGval : (∫ x in (2:ℝ)..y,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x)
        = ∑ n ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt n *
            (S (y / n) - S (max 2 (n : ℝ) / n)) := by
      rw [← intervalIntegral.integral_congr hEq,
        intervalIntegral.integral_finset_sum (fun n hn =>
          intervalIntegrable_term n (Finset.mem_Icc.1 hn).1 hy2 (hMy n hn))]
      exact Finset.sum_congr rfl fun n hn =>
        integral_term n (Finset.mem_Icc.1 hn).1 hy2 (hMy n hn)
    have hA := integral_S_log y hy2
    -- the combined integral, bounded by Selberg's inequality
    have hcomb : (∫ x in (2:ℝ)..y, (((R x / x) * Real.log x + S x / x)
        + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x))
        = S y * Real.log y
          + ∑ n ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt n *
              (S (y / n) - S (max 2 (n : ℝ) / n)) := by
      rw [intervalIntegral.integral_add (intervalIntegrable_F hy2) hGint, hA, hGval]
    have hbound : |∫ x in (2:ℝ)..y, (((R x / x) * Real.log x + S x / x)
        + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x)|
        ≤ (C₀ + 1) * (y - 2) := by
      have hnorm : ∀ x ∈ Set.uIoc (2:ℝ) y, ‖((R x / x) * Real.log x + S x / x)
          + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x‖
          ≤ C₀ + 1 := by
        intro x hx
        rw [Set.uIoc_of_le hy2] at hx
        have hx2 : (2:ℝ) ≤ x := le_of_lt hx.1
        have hx0 : (0:ℝ) < x := by linarith
        have h1 := hsel x (by linarith)
        have hS : |S x| ≤ x - 2 := abs_S_le x hx2
        have hsplit : ((R x / x) * Real.log x + S x / x)
            + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x
            = (R x * Real.log x
                + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x
              + S x / x := by
          field_simp
          ring
        rw [Real.norm_eq_abs, hsplit]
        refine le_trans (abs_add_le _ _) ?_
        have hb1 : |(R x * Real.log x
            + ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x| ≤ C₀ := by
          rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
          exact le_trans h1 (by nlinarith)
        have hb2 : |S x / x| ≤ 1 := by
          rw [abs_div, abs_of_pos hx0, div_le_one hx0]
          linarith
        linarith
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (2:ℝ)) (b := y)
        (C := C₀ + 1) hnorm
      rw [Real.norm_eq_abs] at h
      have : |y - 2| = y - 2 := abs_of_nonneg (by linarith)
      rw [this] at h
      exact h
    -- the boundary terms
    have hbdry : |∑ n ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt n *
        S (max 2 (n : ℝ) / n)| ≤ 4 * y := by
      have hterm : ∀ n ∈ Finset.Icc 1 M,
          |ArithmeticFunction.vonMangoldt n * S (max 2 (n : ℝ) / n)|
            ≤ 2 * ArithmeticFunction.vonMangoldt n := by
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
        have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
        have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
        have hc0 : (0:ℝ) < max 2 (n : ℝ) / n := by positivity
        have hc2 : max 2 (n : ℝ) / n ≤ 2 := by
          rcases max_cases (2:ℝ) (n:ℝ) with ⟨he, _⟩ | ⟨he, _⟩
          · rw [he]
            rw [div_le_iff₀ hn0]
            nlinarith
          · rw [he, div_self (ne_of_gt hn0)]
            norm_num
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have := Stage4cAux.abs_S_le_two hc0 hc2
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
      calc |∑ n ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt n * S (max 2 (n : ℝ) / n)|
          ≤ ∑ n ∈ Finset.Icc 1 M, |ArithmeticFunction.vonMangoldt n * S (max 2 (n : ℝ) / n)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 M, 2 * ArithmeticFunction.vonMangoldt n :=
            Finset.sum_le_sum hterm
        _ = 2 * psi y := by rw [← Finset.mul_sum]; rfl
        _ ≤ 4 * y := by
            have := Stage4aAux.psi_le_two_mul (x := y) (le_of_lt hy0)
            linarith
    -- assembly
    have hkey : S y * Real.log y
        + ∑ n ∈ Finset.Icc 1 M, S (y / n) * ArithmeticFunction.vonMangoldt n
        = (∫ x in (2:ℝ)..y, (((R x / x) * Real.log x + S x / x)
            + (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, R (x / n) * ArithmeticFunction.vonMangoldt n) / x))
          + ∑ n ∈ Finset.Icc 1 M, ArithmeticFunction.vonMangoldt n * S (max 2 (n : ℝ) / n) := by
      rw [hcomb, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hkey]
    refine le_trans (abs_add_le _ _) ?_
    have := abs_le.1 hbound
    linarith [hbound, hbdry]

end Stage4cStep1

end SelbergPNT
