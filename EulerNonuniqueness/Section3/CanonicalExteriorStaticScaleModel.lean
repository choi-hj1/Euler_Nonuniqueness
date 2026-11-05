import EulerNonuniqueness.Section3.CanonicalExteriorStaticRelativeAssembly
import EulerNonuniqueness.General.ExteriorStaticResidualScale

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem canonicalExteriorStaticRelativeBudget_same_le_scale_model
    (frequency : ℝ) (coefficient : ℕ → ℂ)
    (firstBase finalBase firstIncrement finalIncrement firstShift finalShift firstPrimitive finalPrimitive : PeriodicC1HolderHalf)
    (strain : ℂ) {constant epsilon radius ratio transverse angular : ℝ}
    (constantNonnegative : 0 ≤ constant) (epsilonNonnegative : 0 ≤ epsilon)
    (radiusNonnegative : 0 ≤ radius) (ratioNonnegative : 0 ≤ ratio)
    (transverseNonnegative : 0 ≤ transverse) (angularNonnegative : 0 ≤ angular)
    (fullBound : (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) ≤ constant * |frequency| * epsilon)
    (tailBound : (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖exteriorCoefficientWithoutLeading coefficient degree‖) ≤ constant * |frequency| * epsilon * ratio)
    (strainBound : ‖strain‖ ≤ constant * |frequency| * epsilon)
    (incrementSum : ‖firstIncrement‖ + ‖finalIncrement‖ ≤ 2 * constant * radius)
    (firstIncrementBound : ‖firstIncrement‖ ≤ constant * radius)
    (finalIncrementBound : ‖finalIncrement‖ ≤ constant * radius)
    (incrementDifference : ‖firstIncrement - finalIncrement‖ ≤ constant * (transverse + radius * angular))
    (baseDifference : ‖firstBase - finalBase‖ ≤ constant * angular)
    (dataDifference : ‖(firstBase + firstIncrement) - (finalBase + finalIncrement)‖ ≤ constant * (transverse + angular))
    (shiftSum : ‖firstShift‖ + ‖finalShift‖ ≤ 2 * constant * epsilon)
    (shiftDifference : ‖firstShift - finalShift‖ ≤ constant * epsilon * (transverse + angular))
    (finalShiftBound : ‖finalShift‖ ≤ constant * epsilon)
    (primitiveDifference : ‖firstPrimitive - finalPrimitive‖ ≤ constant * epsilon * ratio * angular)
    (finalPrimitiveBound : ‖finalPrimitive‖ ≤ constant * epsilon * ratio) :
    canonicalExteriorStaticRelativeBudget frequency coefficient coefficient firstBase finalBase
      firstIncrement finalIncrement firstShift finalShift firstPrimitive finalPrimitive strain strain ≤
      EulerNonuniqueness.General.exteriorStaticResidualScaleModel |frequency| constant epsilon radius ratio transverse angular := by
  have doubled : (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) +
      (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) ≤ 2 * constant * |frequency| * epsilon := by
    linarith
  unfold canonicalExteriorStaticRelativeBudget EulerNonuniqueness.General.exteriorStaticResidualScaleModel
  simp only [sub_self, norm_zero, mul_zero, zero_mul, tsum_zero, zero_add, add_zero]
  gcongr <;> first | assumption | positivity

end EulerNonuniqueness.Paper
