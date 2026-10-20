import KMS.VirtualOne
import Mathlib.NumberTheory.Real.GoldenRatio

/-! Golden-coordinate setup. The sharp Hurwitz and noble results appear in `KMS/Hurwitz.lean`. -/

namespace ShiftedKMS

noncomputable def goldenFraction : ℝ := Real.goldenRatio - 1
noncomputable def hollowGoldenAlpha : ℝ := 2 - Real.goldenRatio

theorem goldenFraction_irrational : Irrational goldenFraction := by
  simpa [goldenFraction] using Real.goldenRatio_irrational.sub_intCast 1

theorem hollowGoldenAlpha_irrational : Irrational hollowGoldenAlpha := by
  simpa [hollowGoldenAlpha] using Real.goldenRatio_irrational.intCast_sub 2

theorem goldenFraction_pos : 0 < goldenFraction := by
  dsimp [goldenFraction]
  linarith [Real.one_lt_goldenRatio]

theorem hollowGoldenAlpha_pos : 0 < hollowGoldenAlpha := by
  dsimp [hollowGoldenAlpha]
  linarith [Real.goldenRatio_lt_two]

theorem hollowGoldenAlpha_lt_half : hollowGoldenAlpha < 1 / 2 := by
  dsimp [hollowGoldenAlpha, Real.goldenRatio]
  have hsqrt5 : 2 < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sqrt_nonneg 5]
  linarith

theorem hollowGoldenAlpha_add_goldenFraction :
    hollowGoldenAlpha + goldenFraction = 1 := by
  dsimp [hollowGoldenAlpha, goldenFraction]
  ring

end ShiftedKMS
