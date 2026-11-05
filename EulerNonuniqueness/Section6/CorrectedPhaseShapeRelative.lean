import EulerNonuniqueness.Section6.CorrectedPhaseReconstruction

noncomputable section

namespace EulerNonuniqueness.Section6

theorem sameGraph_correctedHalfDiagonalProfile_exists_relative_chart_bound
    {graph coordinate correction : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (correctionSmooth : ContDiffAt ℝ 1 correction 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × (ℝ × ℝ),
      |first.1 - 1| + |first.2.1| + |first.2.2| < radius →
      |second.1 - 1| + |second.2.1| + |second.2.2| < radius →
      ∀ firstPhase secondPhase : ℝ,
      ‖Complex.exp (Complex.I * (firstPhase : ℂ)) • correctedHalfDiagonalProfile correction first -
        Complex.exp (Complex.I * (secondPhase : ℂ)) • correctedHalfDiagonalProfile correction second‖ ≤
      constant * (|first.1 - second.1| +
        |(localNormalFormChart graph coordinate first.2).1 - (localNormalFormChart graph coordinate second.2).1| +
        |(localNormalFormChart graph coordinate first.2).2 - (localNormalFormChart graph coordinate second.2).2| +
        |firstPhase - secondPhase|) := by
  obtain ⟨profileRadius, profilePositive, profileConstant, profileOne, profileBound⟩ :=
    correctedHalfDiagonalProfile_exists_uniform_relative_bound correctionSmooth
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let radius := min profileRadius inverseRadius
  refine ⟨radius, lt_min profilePositive inversePositive, profileConstant * (inverseConstant + 1),
    by nlinarith, ?_⟩
  intro first second firstSmall secondSmall firstPhase secondPhase
  have firstRaw : |first.2.1| + |first.2.2| < inverseRadius :=
    (by linarith [abs_nonneg (first.1 - 1)] : |first.2.1| + |first.2.2| < radius).trans_le (min_le_right _ _)
  have secondRaw : |second.2.1| + |second.2.2| < inverseRadius :=
    (by linarith [abs_nonneg (second.1 - 1)] : |second.2.1| + |second.2.2| < radius).trans_le (min_le_right _ _)
  have inverse := inverseBound first.2 second.2 firstRaw secondRaw
  have chartNorm : ‖localNormalFormChart graph coordinate first.2 - localNormalFormChart graph coordinate second.2‖ ≤
      |(localNormalFormChart graph coordinate first.2).1 - (localNormalFormChart graph coordinate second.2).1| +
        |(localNormalFormChart graph coordinate first.2).2 - (localNormalFormChart graph coordinate second.2).2| := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have rawDifference := inverse.trans (mul_le_mul_of_nonneg_left chartNorm (by linarith : 0 ≤ inverseConstant))
  have estimate := profileBound first second (firstSmall.trans_le (min_le_left _ _))
    (secondSmall.trans_le (min_le_left _ _)) firstPhase secondPhase
  apply estimate.trans
  have profileNonnegative : 0 ≤ profileConstant := by linarith
  have dilationNonnegative := abs_nonneg (first.1 - second.1)
  have phaseNonnegative := abs_nonneg (firstPhase - secondPhase)
  have positiveNonnegative := abs_nonneg ((localNormalFormChart graph coordinate first.2).1 -
    (localNormalFormChart graph coordinate second.2).1)
  have negativeNonnegative := abs_nonneg ((localNormalFormChart graph coordinate first.2).2 -
    (localNormalFormChart graph coordinate second.2).2)
  nlinarith [mul_nonneg profileNonnegative
    (sub_nonneg.mpr rawDifference), mul_nonneg profileNonnegative
      (mul_nonneg (by linarith : 0 ≤ inverseConstant) (add_nonneg dilationNonnegative phaseNonnegative))]

end EulerNonuniqueness.Section6
