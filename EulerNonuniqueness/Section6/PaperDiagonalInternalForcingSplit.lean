import EulerNonuniqueness.Section6.PaperRelativeDiagonalInternalRate
import EulerNonuniqueness.Section6.FourPointDilationDirectional
import EulerNonuniqueness.Section6.PaperSmallShapeDiagonalDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

theorem central_halfDiagonal_dilation_rate_zero (coefficient : ℝ) {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    2 * @inner ℝ ℂ _ positive (positivePointVelocity coefficient positive negative) -
      2 * @inner ℝ ℂ _ negative (negativePointVelocity coefficient positive negative) = 0 := by
  have actual := fourPointDilationDirectionalRate_field_eq_centered coefficient
    (centrallySymmetricFourPoint positive negative) noncollision
  have momentZero : fourPointSignedMoment (centrallySymmetricFourPoint positive negative) = 0 := by
    simp [fourPointSignedMoment, centrallySymmetricFourPoint, fourPointSign, Fin.sum_univ_succ]
  rw [fourPointCenteredDilationRate, momentZero, mul_zero, Complex.zero_re, neg_zero,
    fourPointDilationDirectionalRate, fourPointOddPart_central,
    fourPointOddPart_central_field coefficient noncollision] at actual
  exact actual

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem diagonalOddForcingRate_eq_internal_directional
    {count : ℕ} (scales : Scales) (motion : PatchMotion count) (index : Fin count) (time : ℝ)
    (noncollision : FourPointNoncollision (fun patch => patchCentroid motion time index patch))
    (centralNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index))) :
    diagonalOddForcingRate scales motion index time = quadrupoleInternalDilationRate scales motion index time +
      fourPointDilationDirectionalRate (fun patch => patchCentroid motion time index patch)
        (quadrupoleCentroidForcing scales motion time index) := by
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let positions : FourPointConfiguration := fun patch => patchCentroid motion time index patch
  let full := fourPointOddPart (fourPointField coefficient positions)
  let forcing := fourPointOddPart (quadrupoleCentroidForcing scales motion time index)
  have internal := fourPointDilationDirectionalRate_field_eq_centered coefficient positions noncollision
  have internal' : 2 * @inner ℝ ℂ _ (positiveHalfDiagonal motion time index) full.1 -
      2 * @inner ℝ ℂ _ (negativeHalfDiagonal motion time index) full.2 =
      quadrupoleInternalDilationRate scales motion index time := internal
  have central := central_halfDiagonal_dilation_rate_zero coefficient centralNoncollision
  change 2 * @inner ℝ ℂ _ (positiveHalfDiagonal motion time index)
      (full.1 - positivePointVelocity coefficient (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) + forcing.1) -
    2 * @inner ℝ ℂ _ (negativeHalfDiagonal motion time index)
      (full.2 - negativePointVelocity coefficient (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) + forcing.2) =
    quadrupoleInternalDilationRate scales motion index time +
      (2 * @inner ℝ ℂ _ (positiveHalfDiagonal motion time index) forcing.1 -
        2 * @inner ℝ ℂ _ (negativeHalfDiagonal motion time index) forcing.2)
  simp only [inner_add_right, inner_sub_right]
  linarith

end EulerNonuniqueness.Paper
