import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

theorem finite_state_coefficient_majorants
    {bound omega epsilon strain macroRatio referenceSize tolerance size shape moment center raw
      leadingComponent leadingNorm difference own macroForeign external stableConstant dilationConstant : ℝ}
    (boundOne : 1 ≤ bound) (omegaOne : 1 ≤ omega)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (strainNonnegative : 0 ≤ strain) (strainOne : strain ≤ 1)
    (macroRatioNonnegative : 0 ≤ macroRatio) (macroRatioOne : macroRatio ≤ 1)
    (referenceNonnegative : 0 ≤ referenceSize) (referenceOne : referenceSize ≤ 1)
    (toleranceNonnegative : 0 ≤ tolerance) (toleranceOne : tolerance ≤ 1)
    (shapeNonnegative : 0 ≤ shape) (shapeSize : shape ≤ size)
    (momentNonnegative : 0 ≤ moment) (momentSize : moment ≤ size)
    (centerNonnegative : 0 ≤ center) (centerSize : center ≤ bound * size)
    (rawNonnegative : 0 ≤ raw) (componentNonnegative : 0 ≤ leadingComponent)
    (componentBound : leadingComponent ≤ leadingNorm) (differenceNonnegative : 0 ≤ difference)
    (ownNonnegative : 0 ≤ own) (macroNonnegative : 0 ≤ macroForeign) (externalNonnegative : 0 ≤ external)
    (stableNonnegative : 0 ≤ stableConstant) (stableBound : stableConstant ≤ bound)
    (dilationNonnegative : 0 ≤ dilationConstant) (dilationBound : dilationConstant ≤ bound) :
    let budget := omega * (size + epsilon * raw) +
      (leadingNorm + difference + epsilon * macroForeign + epsilon * own + external)
    let dilationMajorant := tolerance * moment + (tolerance + dilationConstant * strain + dilationConstant * omega * epsilon) * center +
      dilationConstant * omega * epsilon * raw + dilationConstant * difference + dilationConstant * epsilon * own
    let forcingMajorant := leadingComponent + tolerance * (moment + center + shape) +
      stableConstant * omega * epsilon * (center + raw) + stableConstant * epsilon * own +
      stableConstant * macroRatio * (strain * center + difference) + stableConstant * referenceSize * leadingNorm
    0 ≤ dilationMajorant ∧ dilationMajorant ≤ 7 * bound ^ 2 * budget ∧
      0 ≤ forcingMajorant ∧ forcingMajorant ≤ 10 * bound ^ 2 * budget := by
  dsimp only
  let budget := omega * (size + epsilon * raw) + (leadingNorm + difference + epsilon * macroForeign + epsilon * own + external)
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have sizeNonnegative : 0 ≤ size := shapeNonnegative.trans shapeSize
  have leadingNonnegative : 0 ≤ leadingNorm := componentNonnegative.trans componentBound
  have sizePart := mul_nonneg omegaNonnegative sizeNonnegative
  have rawPart := mul_nonneg omegaNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)
  have macroPart := mul_nonneg epsilonNonnegative macroNonnegative
  have ownPart := mul_nonneg epsilonNonnegative ownNonnegative
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have components : omega * size ≤ budget ∧ omega * epsilon * raw ≤ budget ∧
      leadingNorm ≤ budget ∧ difference ≤ budget ∧ epsilon * own ≤ budget := by
    dsimp only [budget]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [sizePart, rawPart, macroPart, ownPart, leadingNonnegative, differenceNonnegative, externalNonnegative]
  have sizeBudget := (le_mul_of_one_le_left sizeNonnegative omegaOne).trans components.1
  have momentBudget := momentSize.trans sizeBudget
  have shapeBudget := shapeSize.trans sizeBudget
  have centerBudget := centerSize.trans (mul_le_mul_of_nonneg_left sizeBudget boundNonnegative)
  have strainCenter := (mul_le_of_le_one_left centerNonnegative strainOne).trans centerBudget
  have epsilonCenter : omega * epsilon * center ≤ bound * budget := by
    have first := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left centerNonnegative epsilonOne) omegaNonnegative
    have second := mul_le_mul_of_nonneg_left centerSize omegaNonnegative
    have third := mul_le_mul_of_nonneg_left components.1 boundNonnegative
    nlinarith only [first, second, third]
  have selfBudget : omega * epsilon * (center + raw) ≤ (bound + 1) * budget := by
    nlinarith only [epsilonCenter, components.2.1]
  have macroBudget : macroRatio * (strain * center + difference) ≤ (bound + 1) * budget := by
    have first := mul_le_of_le_one_left (add_nonneg (mul_nonneg strainNonnegative centerNonnegative) differenceNonnegative) macroRatioOne
    nlinarith only [first, strainCenter, components.2.2.2.1]
  have referenceBudget := (mul_le_of_le_one_left leadingNonnegative referenceOne).trans components.2.2.1
  have toleranceMoment := (mul_le_of_le_one_left momentNonnegative toleranceOne).trans momentBudget
  have toleranceCenter := (mul_le_of_le_one_left centerNonnegative toleranceOne).trans centerBudget
  have toleranceShape := (mul_le_of_le_one_left shapeNonnegative toleranceOne).trans shapeBudget
  have multiply {constant value coefficient : ℝ} (nonnegative : 0 ≤ constant) (bounded : constant ≤ bound)
      (valueBound : value ≤ coefficient * budget) (coefficientNonnegative : 0 ≤ coefficient) :
      constant * value ≤ bound * coefficient * budget :=
    (mul_le_mul_of_nonneg_left valueBound nonnegative).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right bounded (mul_nonneg coefficientNonnegative budgetNonnegative))
  have dilationStrain := multiply dilationNonnegative dilationBound strainCenter boundNonnegative
  have dilationCenter := multiply dilationNonnegative dilationBound epsilonCenter boundNonnegative
  have dilationRaw := multiply (coefficient := 1) dilationNonnegative dilationBound (by simpa only [one_mul] using components.2.1) (by norm_num)
  have dilationDifference := multiply (coefficient := 1) dilationNonnegative dilationBound (by simpa only [one_mul] using components.2.2.2.1) (by norm_num)
  have dilationOwn := multiply (coefficient := 1) dilationNonnegative dilationBound (by simpa only [one_mul] using components.2.2.2.2) (by norm_num)
  have stableSelf := multiply stableNonnegative stableBound selfBudget (by linarith only [boundOne])
  have stableOwn := multiply (coefficient := 1) stableNonnegative stableBound (by simpa only [one_mul] using components.2.2.2.2) (by norm_num)
  have stableMacro := multiply stableNonnegative stableBound macroBudget (by linarith only [boundOne])
  have stableLeading := multiply (coefficient := 1) stableNonnegative stableBound (by simpa only [one_mul] using referenceBudget) (by norm_num)
  have dilationCoefficients : 2 * bound ^ 2 + 4 * bound + 1 ≤ 7 * bound ^ 2 := by
    nlinarith only [boundOne, sq_nonneg (bound - 1)]
  have forcingCoefficients : 2 * bound ^ 2 + 5 * bound + 3 ≤ 10 * bound ^ 2 := by
    nlinarith only [boundOne, sq_nonneg (bound - 1)]
  have dilationFinal := mul_le_mul_of_nonneg_right dilationCoefficients budgetNonnegative
  have forcingFinal := mul_le_mul_of_nonneg_right forcingCoefficients budgetNonnegative
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · change _ ≤ 7 * bound ^ 2 * budget
    nlinarith only [toleranceMoment, toleranceCenter, dilationStrain, dilationCenter, dilationRaw, dilationDifference, dilationOwn, dilationFinal]
  · change _ ≤ 10 * bound ^ 2 * budget
    nlinarith only [componentBound.trans components.2.2.1, toleranceMoment, toleranceCenter, toleranceShape,
      stableSelf, stableOwn, stableMacro, stableLeading, forcingFinal]

end EulerNonuniqueness.General
