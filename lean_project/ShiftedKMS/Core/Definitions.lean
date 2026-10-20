import KMS.Basic

/-! Convenient public abbreviations for the basic shifted KMS definitions.
The incoming KMS.Basic definitions are canonical. No duplicate symbol or matrix definitions. -/
namespace ShiftedKMS

abbrev kmsMatrix := kms
abbrev shiftedKMS := shifted
noncomputable abbrev lowerBand := lowerEdge
noncomputable abbrev upperBand := upperEdge

structure InteriorParameters where
  a : ℝ
  tau : ℝ
  a_pos : 0 < a
  a_lt_one : a < 1
  lower_lt_tau : lowerBand a < tau
  tau_lt_upper : tau < upperBand a

structure TrianglePoint where
  alpha : ℝ
  beta : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  sum_lt_one : alpha + beta < 1

def phaseResidual (p : TrianglePoint) (n : ℕ) : ℝ :=
  (n : ℝ) * p.alpha - p.beta

def IsArithmeticHit (p : TrianglePoint) (n : ℕ) : Prop :=
  ∃ z : ℤ, phaseResidual p n = (z : ℝ)

end ShiftedKMS
