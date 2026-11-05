import EulerNonuniqueness.Section3.MovingStrainAffineRelative
import EulerNonuniqueness.Section3.MovingStrainAffineBaseZero

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem movingStrainAffineResidual_exists_absolute_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ angular : PeriodicC1HolderHalf,
      ∀ (small : ‖angular‖ < 1 / 2), angular ∈ contourContinuousVectorSubmodule →
      let base := fixedRelabelEquivalence angular small standardCircleBanach
      ‖base - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ∀ direction : PeriodicC1HolderHalf, direction ∈ contourContinuousVectorSubmodule →
      ‖base - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      contourCentroidFunctional (base + direction) = contourCentroidFunctional base →
      ∀ coefficient : ℂ,
      ‖movingStrainAffineResidual base coefficient (base + direction)‖ ≤
        constant * ‖coefficient‖ * ‖direction‖ ^ 2 := by
  obtain ⟨radius, positive, constant, nonnegative, bound⟩ :=
    movingStrainAffineResidual_exists_relative_quadratic_ball
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro angular small member base nearby direction directionMember inside centered coefficient
  have joint : ‖base - standardCircleBanach‖ + (‖direction‖ + ‖(0 : PeriodicC1HolderHalf)‖) ≤ radius := by
    simpa only [norm_zero, add_zero] using inside
  have estimate := bound angular angular small small member member nearby nearby direction 0 directionMember
    contourContinuousVectorSubmodule.zero_mem joint joint centered (by simp only [add_zero]) coefficient
  have zero := movingStrainAffineResidual_relabel_base_zero angular small nearby coefficient
  with_reducible_and_instances
    simpa only [add_zero, zero, sub_zero, sub_self, norm_zero, zero_mul, mul_zero, pow_two] using estimate

end EulerNonuniqueness.Paper
