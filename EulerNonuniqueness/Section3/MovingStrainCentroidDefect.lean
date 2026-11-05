import EulerNonuniqueness.Section3.MovingStrainAffineResidual
import EulerNonuniqueness.Section3.ContourCentroidRelativeConstraint
import EulerNonuniqueness.General.ProjectionKernelFactor

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainAffineLinearResidualCLM_eq_centroid_defect
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule) :
    movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach)
        coefficient direction =
      movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach)
        coefficient (c1Constant (fderiv ℝ contourCentroidFunctional
          (fixedRelabelEquivalence angular small standardCircleBanach) direction)) := by
  have projected := movingStrainAffineLinearResidualCLM_projection_zero
    angular small angularMember nearby coefficient direction member
  have projectionEquation := contourCentroidGaugeProjection_apply
    (fixedRelabelEquivalence angular small standardCircleBanach) direction
  with_reducible_and_instances
    exact EulerNonuniqueness.General.linear_eq_defect_of_projection_zero
      (movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach) coefficient)
      _ direction _ projectionEquation projected

theorem movingStrainAffineLinearResidualCLM_eq_centroid_taylor
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (angularMember : angular ∈ contourContinuousVectorSubmodule)
    (nearby : ‖fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule)
    (equalCentroid : contourCentroidFunctional
        (fixedRelabelEquivalence angular small standardCircleBanach + direction) =
      contourCentroidFunctional (fixedRelabelEquivalence angular small standardCircleBanach)) :
    movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach)
        coefficient direction =
      movingStrainAffineLinearResidualCLM (fixedRelabelEquivalence angular small standardCircleBanach)
        coefficient (c1Constant (-contourCentroidTaylorRemainder
          (fixedRelabelEquivalence angular small standardCircleBanach - standardCircleBanach) direction)) := by
  have defect := contourCentroidDerivative_eq_neg_taylor_of_equal_centroid
    (fixedRelabelEquivalence angular small standardCircleBanach) direction
    (lt_min_iff.mp nearby).1 equalCentroid
  have first := movingStrainAffineLinearResidualCLM_eq_centroid_defect
    angular small angularMember nearby coefficient direction member
  exact first.trans (congrArg
    (fun value : ℂ => movingStrainAffineLinearResidualCLM
      (fixedRelabelEquivalence angular small standardCircleBanach) coefficient (c1Constant value)) defect)

end EulerNonuniqueness.Paper
