import EulerNonuniqueness.Section3.CanonicalExteriorCommonMaterialField
import EulerNonuniqueness.General.ZeroGeneratorPairHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

def canonicalExteriorCommonTrueAngularCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskNeutralCLM (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time data)

def canonicalExteriorCommonTrueAngularForcing {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data residual sourceDifference : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf :=
  frequency • diskNeutralCLM (diskSpectralTubularEulerField
    (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time data)) +
  diskNeutralCLM (diskNormalizedSpectralError
    (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data) residual) +
  diskNeutralCLM (family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time data sourceDifference)

theorem canonicalExteriorCommonTrueAngularCoordinate_exists_pair_history_ball :
    ∃ physicalRadius > 0,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency : ℝ)
        (firstCurve finalCurve firstResidual finalResidual sourceDifference : ℝ → PeriodicC1HolderHalf)
        {horizon : ℝ}, 0 ≤ horizon →
      ContinuousOn (fun time => family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (firstCurve time)) (Icc 0 horizon) →
      ContinuousOn (fun time => family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (finalCurve time)) (Icc 0 horizon) →
      ContinuousOn (fun time => family.canonicalExteriorCommonTrueAngularForcing index frequency time
        (firstCurve time) (firstResidual time) 0) (Icc 0 horizon) →
      ContinuousOn (fun time => family.canonicalExteriorCommonTrueAngularForcing index frequency time
        (finalCurve time) (finalResidual time) (sourceDifference time)) (Icc 0 horizon) →
      (∀ time ∈ Ioo 0 horizon,
        ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (firstCurve time) - standardCircleBanach‖ ≤ physicalRadius ∧
        ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (finalCurve time) - standardCircleBanach‖ ≤ physicalRadius ∧
        HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (firstCurve current))
          (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (firstCurve time)) +
            firstResidual time + family.canonicalExteriorCommonPhysicalDerivative index frequency time (firstCurve time) 0) time ∧
        HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (finalCurve current))
          (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (finalCurve time)) +
            finalResidual time + family.canonicalExteriorCommonPhysicalDerivative index frequency time (finalCurve time) (sourceDifference time)) time) →
      ∀ time ∈ Icc 0 horizon,
        family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (finalCurve time) -
          family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (firstCurve time) =
        family.canonicalExteriorCommonTrueAngularCoordinate index frequency 0 (finalCurve 0) -
          family.canonicalExteriorCommonTrueAngularCoordinate index frequency 0 (firstCurve 0) +
        ∫ current in (0 : ℝ)..time,
          family.canonicalExteriorCommonTrueAngularForcing index frequency current
            (finalCurve current) (finalResidual current) (sourceDifference current) -
          family.canonicalExteriorCommonTrueAngularForcing index frequency current
            (firstCurve current) (firstResidual current) 0 ∧
        ‖family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (finalCurve time) -
          family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (firstCurve time)‖ ≤
        ‖family.canonicalExteriorCommonTrueAngularCoordinate index frequency 0 (finalCurve 0) -
          family.canonicalExteriorCommonTrueAngularCoordinate index frequency 0 (firstCurve 0)‖ +
        ∫ current in (0 : ℝ)..time,
          ‖family.canonicalExteriorCommonTrueAngularForcing index frequency current
            (finalCurve current) (finalResidual current) (sourceDifference current) -
          family.canonicalExteriorCommonTrueAngularForcing index frequency current
            (firstCurve current) (firstResidual current) 0‖ := by
  obtain ⟨radius, positive, constant, one, evolution⟩ :=
    canonicalExteriorCommonNormalizedPhysicalCoordinate_exists_material_evolution_ball
  refine ⟨radius, positive, ?_⟩
  intro count family index frequency firstCurve finalCurve firstResidual finalResidual sourceDifference horizon horizonNonnegative
    firstContinuous finalContinuous firstForcingContinuous finalForcingContinuous equations
  have angularEquation (curve : ℝ → PeriodicC1HolderHalf) (residual source : PeriodicC1HolderHalf) (time : ℝ)
      (inside : ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time) - standardCircleBanach‖ ≤ radius)
      (equation : HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
        (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) +
          residual + family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time) source) time) :
      HasDerivAt (fun current => family.canonicalExteriorCommonTrueAngularCoordinate index frequency current (curve current))
        (family.canonicalExteriorCommonTrueAngularForcing index frequency time (curve time) residual source) time := by
    have normalized := (evolution family index residual source inside equation).2.1
    have actual := diskNeutralCLM.hasFDerivAt.comp_hasDerivAt time normalized
    with_reducible_and_instances
      simpa only [canonicalExteriorCommonTrueAngularCoordinate, canonicalExteriorCommonTrueAngularForcing,
        Function.comp_def, map_add, map_smul] using actual
  apply EulerNonuniqueness.General.zeroGenerator_pair_history_of_interior horizonNonnegative
    firstContinuous finalContinuous firstForcingContinuous finalForcingContinuous
  · intro time inside
    have actual := equations time inside
    exact angularEquation firstCurve (firstResidual time) 0 time actual.1 actual.2.2.1
  · intro time inside
    have actual := equations time inside
    exact angularEquation finalCurve (finalResidual time) (sourceDifference time) time actual.2.1 actual.2.2.2

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
