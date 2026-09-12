/-
ElementaryPNT.Stage1bWalk — auxiliary development for `ElementaryPNT.Stage1b`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Stage1bAux

open Filter Topology MeasureTheory

namespace SelbergPNT
namespace Stage1bAux

/-- The `ε`-form of the walk lemma, which is where the work is. -/
theorem walk_bound_eps {W : ℝ → ℝ} {T K M c : ℝ} (hK : 0 < K) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|)
    (hgapM : ∀ a b : ℝ, T ≤ a → a < b → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ M)
    (hgapc : ∀ a b : ℝ, T ≤ a → a < b → W a = 0 → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ c * (b - a))
    {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : T ≤ x) :
    (∫ v in T..x, W v) ≤ M + (c + ε) * (x - T) := by
  have hWc : Continuous W := continuous_of_chord hK.le hchord
  set Φ : ℝ → ℝ := fun t => ∫ v in T..t, W v with hΦdef
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_primitive (fun a b => hWc.intervalIntegrable a b) T
  have hΦT : Φ T = 0 := intervalIntegral.integral_same
  have hΦadd : ∀ p q : ℝ, Φ q = Φ p + ∫ v in p..q, W v := by
    intro p q
    rw [hΦdef]
    simp only
    rw [← intervalIntegral.integral_add_adjacent_intervals (hWc.intervalIntegrable T p)
      (hWc.intervalIntegrable p q)]
  set g : ℝ → ℝ := fun t => M + (c + ε) * (t - T) - Φ t with hgdef
  have hgc : Continuous g := by fun_prop
  by_contra hcon
  push_neg at hcon
  have hxS : x ∈ {t | t ∈ Set.Icc T x ∧ g t < 0} := ⟨⟨hx, le_rfl⟩, by simp [hgdef]; linarith⟩
  set S := {t | t ∈ Set.Icc T x ∧ g t < 0} with hSdef
  have hSne : S.Nonempty := ⟨x, hxS⟩
  have hSbdd : BddBelow S := ⟨T, fun t ht => ht.1.1⟩
  set τ := sInf S with hτdef
  have hTτ : T ≤ τ := le_csInf hSne (fun t ht => ht.1.1)
  have hτx : τ ≤ x := csInf_le hSbdd hxS
  have hgT : 0 ≤ g T := by simp [hgdef, hΦT]; linarith
  -- the first failure is not itself a failure
  have hgτ : 0 ≤ g τ := by
    by_contra hneg
    push_neg at hneg
    have hTlt : T < τ := by
      rcases hTτ.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hneg; linarith
    have hopen : IsOpen {y : ℝ | g y < 0} := isOpen_lt hgc continuous_const
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen τ hneg
    set y := max T (τ - δ / 2) with hy
    have hy1 : T ≤ y := le_max_left _ _
    have hy2 : y < τ := max_lt hTlt (by linarith)
    have hy3 : τ - δ < y := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hyS : y ∈ S :=
      ⟨⟨hy1, by linarith⟩, hball (by rw [Real.ball_eq_Ioo]; constructor <;> linarith)⟩
    have := csInf_le hSbdd hyS
    linarith
  have hbelow : ∀ u : ℝ, T ≤ u → u ≤ τ → 0 ≤ g u := by
    intro u hu1 hu2
    by_contra hneg
    push_neg at hneg
    have huS : u ∈ S := ⟨⟨hu1, by linarith⟩, hneg⟩
    have h1 := csInf_le hSbdd huS
    have h2 : u = τ := le_antisymm hu2 h1
    rw [h2] at hneg
    linarith
  -- the step past the first failure
  obtain ⟨δ, hδpos, hstep⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, τ < u → u ≤ τ + δ → u ≤ x → 0 ≤ g u := by
    by_cases hzτ : W τ = 0
    · -- at a zero the chord condition alone suffices, whatever the zeros just past `τ` do
      refine ⟨2 * ε / K, by positivity, ?_⟩
      intro u hτu huδ hux
      have htri : (∫ v in τ..u, W v) ≤ K * (u - τ) ^ 2 / 2 :=
        integral_le_triangle hτu.le hK.le hzτ hchord
      have h1 : K * (u - τ) ^ 2 / 2 ≤ ε * (u - τ) := by
        have hu' : u - τ ≤ 2 * ε / K := by linarith
        have h2 : K * (u - τ) ≤ 2 * ε := by
          rw [le_div_iff₀ hK] at hu'; linarith
        nlinarith [hτu]
      have hgτ' := hgτ
      have hadd := hΦadd τ u
      simp only [hgdef] at hgτ' ⊢
      nlinarith [hadd, htri, h1, hc, hτu]
    · -- away from a zero, the gap hypothesis applies from the last zero at or before `τ`
      have hopen : IsOpen {v : ℝ | W v ≠ 0} := isOpen_ne_fun hWc continuous_const
      obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 hopen τ hzτ
      refine ⟨δ₁ / 2, by positivity, ?_⟩
      intro u hτu huδ hux
      have hnear : ∀ v : ℝ, τ ≤ v → v < u → W v ≠ 0 := by
        intro v hv1 hv2
        refine hball ?_
        rw [Real.ball_eq_Ioo]
        constructor <;> [linarith; linarith]
      by_cases hz : (Set.Icc T τ ∩ {v : ℝ | W v = 0}).Nonempty
      · have hcompact : IsCompact (Set.Icc T τ ∩ {v : ℝ | W v = 0}) :=
          isCompact_Icc.inter_right (isClosed_eq hWc continuous_const)
        have hαmem : sSup (Set.Icc T τ ∩ {v : ℝ | W v = 0}) ∈
            (Set.Icc T τ ∩ {v : ℝ | W v = 0}) := hcompact.sSup_mem hz
        set α := sSup (Set.Icc T τ ∩ {v : ℝ | W v = 0}) with hαdef
        have hTα : T ≤ α := hαmem.1.1
        have hατ : α ≤ τ := hαmem.1.2
        have hWα : W α = 0 := hαmem.2
        have hαu : α < u := lt_of_le_of_lt hατ hτu
        have hnz : ∀ v : ℝ, α < v → v < u → W v ≠ 0 := by
          intro v hv1 hv2
          rcases le_or_gt τ v with h | h
          · exact hnear v h hv2
          · intro hWv
            have hmem : v ∈ Set.Icc T τ ∩ {v : ℝ | W v = 0} := ⟨⟨by linarith, h.le⟩, hWv⟩
            have := le_csSup hcompact.bddAbove hmem
            linarith
        have hgapbd := hgapc α u hTα hαu hWα hnz
        have hgα := hbelow α hTα hατ
        have hadd := hΦadd α u
        simp only [hgdef] at hgα ⊢
        nlinarith [hgapbd, hadd, hε, hαu]
      · have hnz : ∀ v : ℝ, T < v → v < u → W v ≠ 0 := by
          intro v hv1 hv2 hWv
          rcases le_or_gt v τ with h | h
          · exact hz ⟨v, ⟨⟨hv1.le, h⟩, hWv⟩⟩
          · exact hnear v h.le hv2 hWv
        have hTu : T < u := lt_of_le_of_lt hTτ hτu
        have hgapbd := hgapM T u le_rfl hTu hnz
        have hadd := hΦadd T u
        simp only [hgdef]
        rw [hΦT] at hadd
        nlinarith [hgapbd, hadd, hc, hε, hTu]
  obtain ⟨y, hyS, hylt⟩ := exists_lt_of_csInf_lt hSne (show τ < τ + δ by linarith)
  have hτy : τ ≤ y := csInf_le hSbdd hyS
  have hne : τ ≠ y := by
    intro h
    rw [← h] at hyS
    linarith [hyS.2]
  have := hstep y (lt_of_le_of_ne hτy hne) hylt.le hyS.1.2
  linarith [hyS.2]

/-- The walk lemma, component-free. If every gap to the right of `T` that starts at a zero of `W`
has average at most `c`, and every gap to the right of `T` has integral at most `M`, then the
running integral from `T` is at most `c(x − T) + M`.

The proof is a first-failure argument in `ε`-form (`walk_bound_eps`). For `ε > 0` let
`τ` be the infimum of the set of `t ∈ [T,x]` at which `∫_T^t W ≤ M + (c+ε)(t−T)` fails. The
failure set is relatively open, so the bound still holds at `τ` and everywhere below it, while
failures occur arbitrarily close above `τ`. Both cases at `τ` then contradict that:

* if `W τ = 0`, the chord condition alone gives `∫_τ^u W ≤ K(u−τ)²/2 ≤ ε(u−τ)` for `u ≤ τ + 2ε/K`,
  which is why no assumption about how the zeros of `W` sit just past `τ` is needed;
* if `W τ ≠ 0`, then `W` is nonzero on `(α, u)` for `α` the last zero at or before `τ` and `u`
  just past `τ`, so the per-gap hypothesis applies on `[α, u]`, and `α ≤ τ` carries the bound.

No decomposition of `{W ≠ 0}` into connected components occurs, and no finiteness or ordering of
the zeros is assumed. -/
theorem walk_bound {W : ℝ → ℝ} {T K M c : ℝ} (hK : 0 < K) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hchord : ∀ x y : ℝ, |W x - W y| ≤ K * |x - y|)
    (hgapM : ∀ a b : ℝ, T ≤ a → a < b → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ M)
    (hgapc : ∀ a b : ℝ, T ≤ a → a < b → W a = 0 → (∀ v : ℝ, a < v → v < b → W v ≠ 0) →
      (∫ v in a..b, W v) ≤ c * (b - a)) :
    ∀ x : ℝ, T ≤ x → (∫ v in T..x, W v) ≤ c * (x - T) + M := by
  intro x hx
  rcases eq_or_lt_of_le hx with rfl | hlt
  · simpa using hM
  · refine le_of_forall_pos_le_add ?_
    intro η hη
    have hxT : 0 < x - T := by linarith
    have := walk_bound_eps hK hM hc hchord hgapM hgapc (ε := η / (x - T)) (by positivity) hx
    have hcalc : M + (c + η / (x - T)) * (x - T) = c * (x - T) + M + η := by
      field_simp
      ring
    linarith [hcalc ▸ this]

end Stage1bAux
end SelbergPNT
