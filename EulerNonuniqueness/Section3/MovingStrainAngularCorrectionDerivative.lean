import EulerNonuniqueness.Section3.MovingStrainAffineCoefficient
import EulerNonuniqueness.Section3.RelabeledDiskForcingAnalytic
import EulerNonuniqueness.General.LocalLipschitzBallBounds
import EulerNonuniqueness.General.OperatorPairEvaluation

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

local instance angularCoefficientUniformAdd : IsUniformAddGroup
    (ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup
    (E := ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)

local instance angularCoefficientContinuousAdd : ContinuousAdd
    (ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  (inferInstance : IsTopologicalAddGroup
    (ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)).toContinuousAdd

def movingStrainAngularCoefficient (angular : PeriodicC1HolderHalf) :
    ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  movingStrainCorrectionCoefficient (diskRelabelCurve angular 1)

def movingStrainAngularCorrectionDerivative (angular : PeriodicC1HolderHalf) (strain : ℂ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (ContinuousLinearMap.apply ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) strain).comp
    (fderiv ℝ movingStrainAngularCoefficient angular)

theorem movingStrainAngularCoefficient_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear movingStrainAngularCoefficient
      (0 : PeriodicC1HolderHalf) := by
  have baseZero : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear movingStrainCorrectionCoefficient
      (diskRelabelCurve (0 : PeriodicC1HolderHalf) 1) := by
    rw [baseZero]
    exact movingStrainRealCorrectionCoefficient_hasLipschitzDerivativeNear
  have inner : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun angular => diskRelabelCurve angular 1) (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskRelabelMap_analyticAt 0)
  simpa only [movingStrainAngularCoefficient] using EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
    (outer := movingStrainCorrectionCoefficient) (inner := fun angular => diskRelabelCurve angular 1)
    (point := (0 : PeriodicC1HolderHalf)) outer inner

theorem movingStrainRealCorrectionCLM_hasFDerivAt_angular
    (angular : PeriodicC1HolderHalf) (strain : ℂ)
    (regular : DifferentiableAt ℝ movingStrainAngularCoefficient angular) :
    HasFDerivAt (fun current => movingStrainRealCorrectionCLM (diskRelabelCurve current 1) strain)
      (movingStrainAngularCorrectionDerivative angular strain) angular := by
  have actual := (ContinuousLinearMap.apply ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) strain).hasFDerivAt.comp angular regular.hasFDerivAt
  with_reducible_and_instances
    simpa only [Function.comp_def, movingStrainAngularCoefficient, movingStrainCorrectionCoefficient_apply,
      ContinuousLinearMap.apply_apply, movingStrainAngularCorrectionDerivative] using actual

theorem movingStrainAngularCorrectionDerivative_exists_uniform_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ angular : PeriodicC1HolderHalf, ‖angular‖ ≤ radius →
        DifferentiableAt ℝ movingStrainAngularCoefficient angular) ∧
      (∀ angular : PeriodicC1HolderHalf, ‖angular‖ ≤ radius → ∀ strain : ℂ,
        ‖movingStrainAngularCorrectionDerivative angular strain‖ ≤ constant * ‖strain‖) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖final‖ ≤ radius → ∀ strain : ℂ,
        ‖movingStrainAngularCorrectionDerivative first strain - movingStrainAngularCorrectionDerivative final strain‖ ≤
          constant * ‖strain‖ * ‖first - final‖ := by
  have regular := movingStrainAngularCoefficient_hasLipschitzDerivativeNear
  obtain ⟨derivativeRadius, derivativePositive, constant, one, absolute, difference⟩ :=
    regular.2.exists_closedBall_bounds
  obtain ⟨differentiableRadius, differentiablePositive, differentiable⟩ := Metric.eventually_nhds_iff.mp regular.1
  let radius := min derivativeRadius (differentiableRadius / 2)
  refine ⟨radius, by dsimp [radius]; positivity, constant, one, ?_, ?_, ?_⟩
  · intro angular inside
    apply differentiable
    rw [dist_zero_right]
    exact (inside.trans (min_le_right _ _)).trans_lt (by linarith)
  · intro angular inside strain
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    have evaluation := (fderiv ℝ movingStrainAngularCoefficient angular direction).le_opNorm strain
    have derivative := (fderiv ℝ movingStrainAngularCoefficient angular).le_opNorm direction
    have bound := absolute angular (inside.trans (min_le_left _ _))
    exact (evaluation.trans (mul_le_mul_of_nonneg_right
      (derivative.trans (mul_le_mul_of_nonneg_right bound (norm_nonneg direction))) (norm_nonneg strain))).trans_eq (by ring)
  · intro first final firstInside finalInside strain
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    have operator := difference first final (firstInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _))
    let firstDerivative := fderiv ℝ movingStrainAngularCoefficient first
    let finalDerivative := fderiv ℝ movingStrainAngularCoefficient final
    have derivative := EulerNonuniqueness.General.norm_operator_difference_apply_le
      firstDerivative finalDerivative direction
    have evaluation := EulerNonuniqueness.General.norm_operator_difference_apply_le
      (firstDerivative direction) (finalDerivative direction) strain
    change ‖(fderiv ℝ movingStrainAngularCoefficient first direction) strain -
      (fderiv ℝ movingStrainAngularCoefficient final direction) strain‖ ≤ _
    with_reducible_and_instances
      exact (evaluation.trans (mul_le_mul_of_nonneg_right
        (derivative.trans (mul_le_mul_of_nonneg_right operator (norm_nonneg direction))) (norm_nonneg strain))).trans_eq (by ring)

end EulerNonuniqueness.Paper
