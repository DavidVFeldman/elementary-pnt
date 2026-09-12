/-
Axiom audit. Every declaration below must depend on at most `propext`, `Classical.choice` and
`Quot.sound`; in particular on no `sorryAx`.
-/
import ElementaryPNT
open SelbergPNT
-- the theorem
#print axioms primeCounting_asymptotic
#print axioms psi_asymptotic
-- Stage 1
#print axioms tendsto_div_of_tendsto_integral_div
#print axioms monotone_R_add_id
#print axioms log_factorial_sub_two_le
#print axioms psi_isBigO
#print axioms mertens
#print axioms tatuzawa_iseki
-- Stage 1b
#print axioms gap_integral_le_min
#print axioms integral_min_ramp
#print axioms gap_average_le
#print axioms average_le_of_gaps
#print axioms average_le_of_gaps_essential
#print axioms tendsto_zero_of_three_conditions
-- Stage 3
#print axioms Mtr_F1_sub_log_factorial_isBigO
#print axioms Mtr_FS_isBigO
#print axioms selberg_first
#print axioms selberg_psi_form
#print axioms sum_vonMangoldt_mul_log
#print axioms selberg_second
#print axioms selberg_second'
-- Stage 4
#print axioms abs_R_le
#print axioms abs_S_le
#print axioms limsup_abs_S_div_le_one
#print axioms abs_W_le_one
#print axioms S_lipschitz
#print axioms W_lipschitz_nonneg
#print axioms Wtr_properties
#print axioms Wtr_agrees
#print axioms integral_psi_div_sq_isBigO
#print axioms integral_S_div_sq
#print axioms integral_S_div_sq_bounded
#print axioms Wtr_integral_bound
#print axioms integral_mul_sub_eq_integral_integral
#print axioms alpha_le_kappa_tr
#print axioms W_tendsto_zero_of_smoothing
#print axioms S_div_tendsto_zero_of_smoothing
#print axioms selberg_S_form_const
#print axioms S_log_sq_eq_const
#print axioms abs_S_log_sq_le_sum_const
#print axioms abs_S_log_sq_le_integral_const
#print axioms W_le_average
-- Stage 5
#print axioms psi_asymptotic_of_S
#print axioms primeCounting_asymptotic_of_psi
-- Chebyshev, including the two results Mathlib lacks
#print axioms ElementaryPNT.psi_eq_chebyshevPsi
#print axioms ElementaryPNT.log_factorial_eq_sum_vonMangoldt_mul_div
