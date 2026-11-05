import EulerNonuniqueness.Section3.MovingStrainAffineTaylorIdentity
import EulerNonuniqueness.Section3.DiskRotatingPhysicalRelativeTaylor

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

theorem movingStrainAffineTaylorRemainder_eq_named_jets
    (base : PeriodicC1HolderHalf) (coefficient : ℂ) (direction : PeriodicC1HolderHalf) :
    movingStrainAffineTaylorRemainder base coefficient direction =
      projectedComplexStrainTaylorRemainder base coefficient direction +
        diskRotatingDerivativeTaylorRemainder base direction (movingStrainRealPrimitiveValue base coefficient) +
        (fderiv ℝ diskEulerRotatingField (base + direction) - fderiv ℝ diskEulerRotatingField base)
          (movingStrainRealCorrectionCLM base coefficient direction) -
        movingStrainRealCorrectionCLM base coefficient (diskRotatingTaylorRemainder base direction) := by
  unfold movingStrainAffineTaylorRemainder diskRotatingDerivativeTaylorRemainder diskRotatingTaylorRemainder
  with_reducible_and_instances rfl

end EulerNonuniqueness.Paper
