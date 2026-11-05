import EulerNonuniqueness.General.FiniteStateCoefficientMajorants

noncomputable section

namespace EulerNonuniqueness.General

theorem finite_state_neutral_history_majorants
    {bound omega epsilon strain ratio size shape dilation moment center raw leading difference own macroForeign external
      momentConstant dilationConstant phaseConstant centerConstant : ℝ}
    (boundOne : 1 ≤ bound) (omegaOne : 1 ≤ omega)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (strainNonnegative : 0 ≤ strain) (strainOne : strain ≤ 1)
    (_ratioNonnegative : 0 ≤ ratio) (ratioOne : ratio ≤ 1)
    (shapeNonnegative : 0 ≤ shape) (shapeSize : shape ≤ size)
    (_dilationNonnegative : 0 ≤ dilation) (dilationSize : dilation ≤ size)
    (momentNonnegative : 0 ≤ moment) (momentSize : moment ≤ size)
    (centerNonnegative : 0 ≤ center) (centerSize : center ≤ bound * size)
    (rawNonnegative : 0 ≤ raw) (leadingNonnegative : 0 ≤ leading)
    (differenceNonnegative : 0 ≤ difference) (ownNonnegative : 0 ≤ own)
    (macroNonnegative : 0 ≤ macroForeign) (externalNonnegative : 0 ≤ external)
    (momentConstantNonnegative : 0 ≤ momentConstant) (momentBound : momentConstant ≤ bound)
    (dilationConstantNonnegative : 0 ≤ dilationConstant) (dilationBound : dilationConstant ≤ bound)
    (phaseConstantNonnegative : 0 ≤ phaseConstant) (phaseBound : phaseConstant ≤ bound)
    (centerConstantNonnegative : 0 ≤ centerConstant) (centerBound : centerConstant ≤ bound) :
    let budget := omega * (size + epsilon * raw) + (leading + difference + epsilon * macroForeign + epsilon * own + external)
    momentConstant * (strain * center + difference + epsilon * (strain * raw + macroForeign)) ≤ 7 * bound ^ 2 * budget ∧
    moment + (1 + dilationConstant * strain + dilationConstant * omega * epsilon) * center +
      dilationConstant * omega * epsilon * raw + dilationConstant * difference + dilationConstant * epsilon * own ≤ 7 * bound ^ 2 * budget ∧
    2 * omega * dilation + omega * shape + (moment + center + shape) +
      phaseConstant * omega * epsilon * (center + raw) + phaseConstant * difference + phaseConstant * epsilon * own ≤ 13 * bound ^ 2 * budget ∧
    moment + center + external + centerConstant * omega * ratio * epsilon * (center + raw) +
      centerConstant * ratio * epsilon * own ≤ 11 * bound ^ 2 * budget := by
  let budget := omega * (size + epsilon * raw) + (leading + difference + epsilon * macroForeign + epsilon * own + external)
  have sizeNonnegative : 0 ≤ size := shapeNonnegative.trans shapeSize
  have nonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have omegaPart : omega * size ≤ budget := by dsimp only [budget]; nlinarith only [mul_nonneg (zero_le_one.trans omegaOne) (mul_nonneg epsilonNonnegative rawNonnegative), leadingNonnegative, differenceNonnegative, mul_nonneg epsilonNonnegative macroNonnegative, mul_nonneg epsilonNonnegative ownNonnegative, externalNonnegative]
  have generic (stable scale : ℝ) (stableNonnegative : 0 ≤ stable) (stableBound : stable ≤ bound)
      (scaleNonnegative : 0 ≤ scale) (scaleBound : scale ≤ bound) :=
    finite_state_coefficient_majorants boundOne omegaOne epsilonNonnegative epsilonOne strainNonnegative strainOne
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl shapeNonnegative shapeSize momentNonnegative momentSize centerNonnegative centerSize
      rawNonnegative (by norm_num : (0 : ℝ) ≤ 0) leadingNonnegative differenceNonnegative ownNonnegative macroNonnegative
      externalNonnegative stableNonnegative stableBound scaleNonnegative scaleBound
  have swapped := finite_state_coefficient_majorants boundOne omegaOne epsilonNonnegative epsilonOne strainNonnegative strainOne
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) shapeNonnegative shapeSize momentNonnegative momentSize centerNonnegative centerSize
    rawNonnegative (by norm_num : (0 : ℝ) ≤ 0) leadingNonnegative differenceNonnegative macroNonnegative ownNonnegative externalNonnegative
    (by norm_num : (0 : ℝ) ≤ 0) (zero_le_one.trans boundOne) momentConstantNonnegative momentBound
  dsimp only at swapped
  have momentUpper : momentConstant * (strain * center + difference + epsilon * (strain * raw + macroForeign)) ≤
      7 * bound ^ 2 * budget := by
    have rawBound := mul_le_mul_of_nonneg_right (strainOne.trans omegaOne) (mul_nonneg (mul_nonneg momentConstantNonnegative epsilonNonnegative) rawNonnegative)
    have extra := mul_nonneg (mul_nonneg (mul_nonneg momentConstantNonnegative (zero_le_one.trans omegaOne)) epsilonNonnegative) centerNonnegative
    dsimp only [budget]
    nlinarith only [swapped.2.1, rawBound, extra]
  have dilationUpper := (generic phaseConstant dilationConstant phaseConstantNonnegative phaseBound dilationConstantNonnegative dilationBound).2.1
  have phaseUpper := (generic phaseConstant dilationConstant phaseConstantNonnegative phaseBound dilationConstantNonnegative dilationBound).2.2.2
  have translationUpper := (generic centerConstant dilationConstant centerConstantNonnegative centerBound dilationConstantNonnegative dilationBound).2.2.2
  simp only [zero_mul, one_mul, zero_add, add_zero] at dilationUpper phaseUpper translationUpper
  have shapePart := (mul_le_mul_of_nonneg_left shapeSize (zero_le_one.trans omegaOne)).trans omegaPart
  have dilationPart := (mul_le_mul_of_nonneg_left dilationSize (zero_le_one.trans omegaOne)).trans omegaPart
  have externalPart : external ≤ budget := by dsimp only [budget]; nlinarith only [mul_nonneg (zero_le_one.trans omegaOne) (add_nonneg sizeNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)), leadingNonnegative, differenceNonnegative, mul_nonneg epsilonNonnegative macroNonnegative, mul_nonneg epsilonNonnegative ownNonnegative]
  have ratioSelf := mul_le_mul_of_nonneg_right ratioOne (mul_nonneg (mul_nonneg (mul_nonneg centerConstantNonnegative (zero_le_one.trans omegaOne)) epsilonNonnegative) (add_nonneg centerNonnegative rawNonnegative))
  have ratioOwn := mul_le_mul_of_nonneg_right ratioOne (mul_nonneg (mul_nonneg centerConstantNonnegative epsilonNonnegative) ownNonnegative)
  have boundSquare : 1 ≤ bound ^ 2 := one_le_pow₀ boundOne
  have slack := mul_le_mul_of_nonneg_right boundSquare nonnegative
  dsimp only [budget] at nonnegative omegaPart shapePart dilationPart externalPart slack
  dsimp only
  refine ⟨momentUpper, by simpa only [one_mul] using dilationUpper, ?_, ?_⟩
  · nlinarith only [phaseUpper, shapePart, dilationPart, slack, mul_nonneg (mul_nonneg phaseConstantNonnegative strainNonnegative) centerNonnegative]
  · nlinarith only [translationUpper, ratioSelf, ratioOwn, externalPart, slack, shapeNonnegative,
      mul_nonneg (mul_nonneg centerConstantNonnegative strainNonnegative) centerNonnegative,
      mul_nonneg centerConstantNonnegative differenceNonnegative]

end EulerNonuniqueness.General

