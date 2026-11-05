import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

theorem finite_state_additive_majorant
    {bound omega epsilon strain macroRatio referenceSize tolerance smallness size shape moment center raw
      dilation leadingNorm difference own stableConstant : ℝ}
    (boundOne : 1 ≤ bound) (omegaOne : 1 ≤ omega) (smallnessNonnegative : 0 ≤ smallness)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : omega * epsilon ≤ smallness)
    (strainNonnegative : 0 ≤ strain) (strainOne : strain ≤ 1)
    (macroRatioNonnegative : 0 ≤ macroRatio) (macroRatioSmall : macroRatio ≤ smallness)
    (referenceNonnegative : 0 ≤ referenceSize) (referenceSmall : omega * referenceSize ≤ smallness)
    (toleranceNonnegative : 0 ≤ tolerance) (toleranceSmall : tolerance ≤ smallness)
    (shapeNonnegative : 0 ≤ shape) (shapeSize : shape ≤ size)
    (momentNonnegative : 0 ≤ moment) (momentSize : moment ≤ size)
    (centerNonnegative : 0 ≤ center) (centerSize : center ≤ bound * size)
    (dilationNonnegative : 0 ≤ dilation) (dilationSize : dilation ≤ size)
    (rawNonnegative : 0 ≤ raw) (leadingNonnegative : 0 ≤ leadingNorm)
    (differenceNonnegative : 0 ≤ difference) (ownNonnegative : 0 ≤ own)
    (stableNonnegative : 0 ≤ stableConstant) (stableBound : stableConstant ≤ bound) :
    let additive := tolerance * (moment + center + shape) +
      stableConstant * omega * epsilon * (center + raw) + stableConstant * epsilon * own +
      stableConstant * macroRatio * (strain * center + difference) + stableConstant * referenceSize * leadingNorm +
      stableConstant * omega * referenceSize * dilation
    0 ≤ additive ∧ additive ≤ 6 * bound ^ 2 * smallness * (size + raw + own + difference + leadingNorm) := by
  dsimp only
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have sizeNonnegative : 0 ≤ size := shapeNonnegative.trans shapeSize
  have epsilonBound : epsilon ≤ smallness :=
    (le_mul_of_one_le_left epsilonNonnegative omegaOne).trans epsilonSmall
  have referenceBound : referenceSize ≤ smallness :=
    (le_mul_of_one_le_left referenceNonnegative omegaOne).trans referenceSmall
  have toleranceTerm : tolerance * (moment + center + shape) ≤ smallness * (bound + 2) * size := by
    have first := mul_le_mul_of_nonneg_right toleranceSmall (by positivity : 0 ≤ moment + center + shape)
    have second := mul_le_mul_of_nonneg_left (add_le_add (add_le_add momentSize centerSize) shapeSize) smallnessNonnegative
    nlinarith only [first, second]
  have centerTerm : stableConstant * omega * epsilon * center ≤ bound ^ 2 * smallness * size := by
    calc
      _ = stableConstant * (omega * epsilon) * center := by ring
      _ ≤ bound * smallness * (bound * size) :=
        mul_le_mul (mul_le_mul stableBound epsilonSmall (mul_nonneg (zero_le_one.trans omegaOne) epsilonNonnegative) boundNonnegative)
          centerSize centerNonnegative (mul_nonneg boundNonnegative smallnessNonnegative)
      _ = _ := by ring
  have rawTerm : stableConstant * omega * epsilon * raw ≤ bound * smallness * raw :=
    mul_le_mul_of_nonneg_right (by
      simpa only [mul_assoc] using mul_le_mul stableBound epsilonSmall
        (mul_nonneg (zero_le_one.trans omegaOne) epsilonNonnegative) boundNonnegative) rawNonnegative
  have ownTerm : stableConstant * epsilon * own ≤ bound * smallness * own :=
    mul_le_mul_of_nonneg_right (mul_le_mul stableBound epsilonBound epsilonNonnegative boundNonnegative) ownNonnegative
  have strainCenter : strain * center ≤ bound * size :=
    (mul_le_of_le_one_left centerNonnegative strainOne).trans centerSize
  have macroTerm : stableConstant * macroRatio * (strain * center + difference) ≤
      bound ^ 2 * smallness * size + bound * smallness * difference := by
    have estimate := mul_le_mul (mul_le_mul stableBound macroRatioSmall macroRatioNonnegative boundNonnegative)
      (add_le_add_right strainCenter difference) (add_nonneg (mul_nonneg strainNonnegative centerNonnegative) differenceNonnegative)
      (mul_nonneg boundNonnegative smallnessNonnegative)
    nlinarith only [estimate]
  have leadingTerm : stableConstant * referenceSize * leadingNorm ≤ bound * smallness * leadingNorm :=
    mul_le_mul_of_nonneg_right (mul_le_mul stableBound referenceBound referenceNonnegative boundNonnegative) leadingNonnegative
  have dilationTerm : stableConstant * omega * referenceSize * dilation ≤ bound * smallness * size := by
    have estimate := mul_le_mul (mul_le_mul stableBound referenceSmall
      (mul_nonneg (zero_le_one.trans omegaOne) referenceNonnegative) boundNonnegative)
      dilationSize dilationNonnegative (mul_nonneg boundNonnegative smallnessNonnegative)
    simpa only [mul_assoc] using estimate
  have sizeCoefficient : 2 * bound ^ 2 + 2 * bound + 2 ≤ 6 * bound ^ 2 := by
    nlinarith only [boundOne, sq_nonneg (bound - 1)]
  have otherCoefficient : bound ≤ 6 * bound ^ 2 := by
    nlinarith only [boundOne, sq_nonneg (bound - 1)]
  have sizeFinal := mul_le_mul_of_nonneg_right sizeCoefficient (mul_nonneg smallnessNonnegative sizeNonnegative)
  have otherFinal := mul_le_mul_of_nonneg_right otherCoefficient
    (mul_nonneg smallnessNonnegative (by positivity : 0 ≤ raw + own + difference + leadingNorm))
  refine ⟨by positivity, ?_⟩
  nlinarith only [toleranceTerm, centerTerm, rawTerm, ownTerm, macroTerm, leadingTerm, dilationTerm, sizeFinal, otherFinal]

end EulerNonuniqueness.General
