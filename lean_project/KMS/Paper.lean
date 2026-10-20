import KMS.Strata
import KMS.Examples

/-!
# `KMS.Paper` — the whole manuscript, end to end

Root of the formalization of C. Dorsey, *Diophantine singularity and conditioning of shifted
Kac–Murdock–Szegő matrices* (accompanying paper). Importing this file supplies the results used there.

Every theorem-like environment of the manuscript is re-exported below under the name
`ShiftedKMS.Paper.<label>` (label as in the TeX source, `:`/`-` replaced by `_`), as an `alias`
of the proved declaration — so `#print axioms ShiftedKMS.Paper.<label>` inspects the manuscript
statement directly. Conventions are the manuscript's: `T_N(a) = [a^{|i-j|}]`, `B_N = T_N - τI`,
`α = θ_τ/π`, `β = 1 - ψ_a(θ_τ)/π`, `d_N = ‖Nα - β‖` (nearest-integer distance, `distZ`),
`α = p/q` in lowest terms where the manuscript says so, positive dimensions `N`.

Supplementary statements formalized in addition to the numbered environments: the three worked
examples, the hollow constants and collapses of §`sec:resonance`, Weyl's and Cassels' theorems
(proved here, not imported), and `card_windowStar` (`L^* ∈ {L-1, L}`).
-/

namespace ShiftedKMS

namespace Paper

-- §2 KMS quantization and Blaschke phase
alias lem_phase := ShiftedKMS.lem_phase
alias prop_blaschke := ShiftedKMS.blaschke_phase
alias prop_blaschke_quant := ShiftedKMS.blaschke_quant
alias thm_quant := ShiftedKMS.eigAngle_existsUnique
alias thm_quant_spacing := ShiftedKMS.eigAngle_spacing
alias thm_quant_eigenpair := ShiftedKMS.kms_eigenpair
alias thm_quant_shifted := ShiftedKMS.shifted_eigenpair
alias thm_quant_spectrum := ShiftedKMS.kms_spectrum
-- §3 The Diophantine triangle and the determinant
alias thm_triangle := ShiftedKMS.triangle_bijOn
alias thm_triangle_forward := ShiftedKMS.triangle_forward
alias thm_triangle_inverse := ShiftedKMS.triangle_inverse
alias lem_chebshift := ShiftedKMS.lem_chebshift
alias thm_det := ShiftedKMS.thm_det
alias thm_det_depth := ShiftedKMS.thm_detdepth
-- §4 Exact singularity geometry and recurrence
alias thm_sing := ShiftedKMS.thm_sing
alias thm_sing_dN := ShiftedKMS.thm_sing_dN
alias thm_sing_nullity := ShiftedKMS.shifted_nullity_one
alias thm_rational_compat := ShiftedKMS.thm_rational_compat
alias thm_rational_congruence := ShiftedKMS.thm_rational_congr
alias thm_rational_one_class := ShiftedKMS.thm_rational_one_class
alias thm_rational_exists := ShiftedKMS.thm_rational_exists
alias thm_rational_recurrent := ShiftedKMS.singDims_infinite
alias thm_rational_empty := ShiftedKMS.singDims_empty
alias cor_param := ShiftedKMS.cor_param
alias cor_param_converse := ShiftedKMS.cor_param_converse
alias example_recurrent_nonhollow := ShiftedKMS.example_golden
alias thm_zeroinf := ShiftedKMS.thm_zeroinf
alias thm_zeroinf_irrational := ShiftedKMS.singDims_subsingleton_of_irrational
alias thm_dense_strata := ShiftedKMS.thm_dense_strata_triangle
alias thm_dense_strata_physical := ShiftedKMS.thm_dense_strata_physical
alias prop_inertia := ShiftedKMS.thm_inertia
alias prop_inertia_zeroCount := ShiftedKMS.thm_zeroCount
alias prop_inertia_sum := ShiftedKMS.thm_inertia_sum
alias prop_kernel := ShiftedKMS.shifted_ker_eq_span
-- §5 Conditioning across the symbol band
alias thm_localization := ShiftedKMS.thm_localization
alias thm_localization_asymp := ShiftedKMS.thm_local_asymp
alias thm_smin := ShiftedKMS.thm_smin_relative
alias thm_smin_ratio := ShiftedKMS.smin_ratio
alias eq_gamma_form := ShiftedKMS.gam_form
alias eq_smax := ShiftedKMS.thm_smax
alias eq_smax_general := ShiftedKMS.thm_smax_general
alias thm_kappa := ShiftedKMS.thm_kappa_relative
alias thm_outside_lower := ShiftedKMS.thm_outside_lower
alias thm_outside_upper := ShiftedKMS.thm_outside_upper
alias thm_edges_up_smin := ShiftedKMS.thm_edge_upper_smin
alias thm_edges_up_kappa := ShiftedKMS.thm_edge_upper_kappa
alias thm_edges_low_smin := ShiftedKMS.thm_edge_lower_smin
alias thm_edges_low_kappa := ShiftedKMS.thm_edge_lower_kappa
alias thm_main_conditioning := ShiftedKMS.thm_main_conditioning
-- §6 Arithmetic laws for interior conditioning
alias thm_rational_laws := ShiftedKMS.thm_rational_laws
alias thm_rational_laws_incompat := ShiftedKMS.thm_rational_laws_incompat
alias thm_rational_laws_compat := ShiftedKMS.thm_rational_laws_compat
alias example_rational_incompatible := ShiftedKMS.example_incompat
alias weyl := ShiftedKMS.weyl_equidistribution
alias thm_irr_laws_dN := ShiftedKMS.dN_law
alias thm_irr_laws_uniform := ShiftedKMS.thm_irr_laws_uniform
alias thm_irr_laws_pareto := ShiftedKMS.thm_irr_laws_pareto
alias thm_irr_laws_paretotail := ShiftedKMS.paretoLaw_tail
alias thm_irr_laws_Lstar := ShiftedKMS.card_windowStar
alias thm_irr_laws_cesaro := ShiftedKMS.thm_irr_laws_cesaro
alias thm_quadratic_envelope := ShiftedKMS.thm_quadratic_envelope
alias thm_exponent := ShiftedKMS.thm_exponent
alias eq_cassels := ShiftedKMS.casselsSupplier
alias eq_genericM := ShiftedKMS.ae_Mplus_eq_zero
alias eq_genericw := ShiftedKMS.ae_wplus_eq_one
alias borel_cantelli := ShiftedKMS.ae_eventually_not_lt_rpow
alias thm_generic := ShiftedKMS.thm_generic
-- §7 The resonant hollow slice
alias thm_resonance := ShiftedKMS.thm_resonance
alias cor_hollowdich_dN := ShiftedKMS.cor_hollowdich_dN
alias cor_hollowdich_rational := ShiftedKMS.cor_hollowdich_rational
alias cor_hollowdich_irrational := ShiftedKMS.cor_hollowdich_irrational
alias prop_affinecollapse := ShiftedKMS.prop_affinecollapse
alias prop_affinecollapse_Mhom := ShiftedKMS.prop_affinecollapse_Mplus
alias example_isolated_irrational := ShiftedKMS.example_isolated
alias eq_hollow_constants := ShiftedKMS.hollow_constants
alias eq_hollowkappa := ShiftedKMS.hollow_kappa
alias hollow_kernel := ShiftedKMS.hollow_kernel_vector
alias hollow_det := ShiftedKMS.hollow_det

end Paper

end ShiftedKMS
