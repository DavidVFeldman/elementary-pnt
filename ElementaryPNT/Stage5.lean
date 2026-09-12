/-
ElementaryPNT.Stage5 — Stage 5: the two bridges, from `S(x)/x → 0` to `ψ(x) ∼ x` to `π(x) ∼ x/log x`.

Part of a formalization of the elementary (Erdős–Selberg) proof of the prime number theorem,
following D. V. Feldman, "1896/1949 — The Elementary Proof of the Prime Number Theorem".
See the repository README for the correspondence between the chapter and these files.
-/
import Mathlib
import ElementaryPNT.Defs
import ElementaryPNT.Stage1
import ElementaryPNT.Stage5Aux

open Filter Topology

namespace SelbergPNT

/-- (chapter step S5.4).
`S(x)/x → 0` implies `ψ(x)/x → 1`.

Chapter proof, `limsup` half: set `B(y,ε) = (1/y)∫_y^{y(1+ε)} R(x)/x dx`. Since `ψ` is monotone,
`∫_y^{y(1+ε)} R(x)/x dx ≥ (ψ(y)/(y(1+ε)) − 1) yε`, whence
`ψ(y)/y ≤ (B/ε + 1)(1+ε)`. The hypothesis makes `B(y,ε) → 0` as `y → ∞` for each fixed `ε`,
since `B(y,ε) = ((1+ε)·S(y(1+ε))/(y(1+ε))) − S(y)/y`; so `limsup ψ(y)/y ≤ (1+ε)` for every `ε`.
The `liminf` half is the same argument on `[y(1−ε), y]`, which the chapter leaves as an exercise;
it gives `liminf ψ(y)/y ≥ (1−ε)/(1+ε)` or better.

Note `R = ψ − id` and `S(x) = ∫₂^x R(u)/u du` are the definitions in `PNT/Defs.lean`, and
`monotone_R_add_id`  is the monotonicity of `ψ`. -/
theorem psi_asymptotic_of_S (hS : Tendsto (fun x : ℝ => S x / x) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => psi x / x) atTop (𝓝 1) :=
  tendsto_of_le_liminf_of_limsup_le (Stage5Aux.one_le_liminf_psi_div hS)
    (Stage5Aux.limsup_psi_div_le_one hS) Stage5Aux.psi_div_isBoundedUnder
    Stage5Aux.psi_div_isBoundedUnder_ge

/-- (chapter step S5.5).
`ψ(x)/x → 1` implies `π(x)/(x/log x) → 1`.

Route: `ψ` and Chebyshev's `θ` differ by `O(√x log² x)`, and
`Chebyshev.primeCounting_sub_theta_div_log_isBigO` relates `π` to `θ/log`. Mathlib supplies both
links; the chapter's §"The equivalence" gives the classical partial-summation argument if they do
not suffice. `Chebyshev.psi_eq_chebyshevPsi` identifies this file's `psi` with Mathlib's. -/
theorem primeCounting_asymptotic_of_psi
    (hpsi : Tendsto (fun x : ℝ => psi x / x) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
  have h := (Stage5Aux.primeCounting_div_tendsto_one
    (Stage5Aux.theta_div_tendsto_one hpsi)).comp tendsto_natCast_atTop_atTop
  refine h.congr ?_
  intro n
  simp

end SelbergPNT
