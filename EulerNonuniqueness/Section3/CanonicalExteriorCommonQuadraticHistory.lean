import EulerNonuniqueness.Section3.CanonicalExteriorCommonQuadraticEvolution
import EulerNonuniqueness.General.CommonLinearPairHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

def canonicalExteriorCommonQuadraticMaterialForcing {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data residual sourceDifference : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf :=
  frequency • diskSpectralMovingSelfRemainder
    (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time data) +
  fderiv ℝ diskSpectralQuadraticObservable
    (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time data)
      (diskNormalizedSpectralError (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data) residual) +
  family.canonicalExteriorCommonQuadraticSourceOperator index frequency time data sourceDifference

theorem canonicalExteriorCommonQuadraticCoordinate_exists_pair_history_ball :
    ∃ physicalRadius > 0, ∃ spectralRadius > 0,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency : ℝ)
        (firstCurve finalCurve firstResidual finalResidual sourceDifference : ℝ → PeriodicC1HolderHalf)
        {horizon : ℝ}, 0 ≤ horizon →
      ContinuousOn (fun time => family.canonicalExteriorCommonQuadraticCoordinate index frequency time (firstCurve time)) (Icc 0 horizon) →
      ContinuousOn (fun time => family.canonicalExteriorCommonQuadraticCoordinate index frequency time (finalCurve time)) (Icc 0 horizon) →
      ContinuousOn (fun time => family.canonicalExteriorCommonQuadraticMaterialForcing index frequency time
        (firstCurve time) (firstResidual time) 0) (Icc 0 horizon) →
      ContinuousOn (fun time => family.canonicalExteriorCommonQuadraticMaterialForcing index frequency time
        (finalCurve time) (finalResidual time) (sourceDifference time)) (Icc 0 horizon) →
      (∀ time ∈ Ioo 0 horizon,
        ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (firstCurve time) - standardCircleBanach‖ ≤ physicalRadius ∧
        ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (finalCurve time) - standardCircleBanach‖ ≤ physicalRadius ∧
        ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (firstCurve time)‖ ≤ spectralRadius ∧
        ‖family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (finalCurve time)‖ ≤ spectralRadius ∧
        HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (firstCurve current))
          (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (firstCurve time)) +
            firstResidual time) time ∧
        HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (finalCurve current))
          (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (finalCurve time)) +
            finalResidual time + family.canonicalExteriorCommonPhysicalDerivative index frequency time (finalCurve time)
              (sourceDifference time)) time) →
      ∀ time ∈ Icc 0 horizon,
      ‖family.canonicalExteriorCommonQuadraticCoordinate index frequency time (finalCurve time) -
        family.canonicalExteriorCommonQuadraticCoordinate index frequency time (firstCurve time)‖ ≤ diskPhysicalGroupBound *
        (‖family.canonicalExteriorCommonQuadraticCoordinate index frequency 0 (finalCurve 0) -
          family.canonicalExteriorCommonQuadraticCoordinate index frequency 0 (firstCurve 0)‖ +
          ∫ current in (0 : ℝ)..time,
            ‖family.canonicalExteriorCommonQuadraticMaterialForcing index frequency current
                (finalCurve current) (finalResidual current) (sourceDifference current) -
              family.canonicalExteriorCommonQuadraticMaterialForcing index frequency current
                (firstCurve current) (firstResidual current) 0‖) := by
  obtain ⟨physicalRadius, physicalPositive, spectralRadius, spectralPositive, _, _, evolution⟩ :=
    canonicalExteriorCommonQuadraticCoordinate_exists_material_evolution_ball
  refine ⟨physicalRadius, physicalPositive, spectralRadius, spectralPositive, ?_⟩
  intro count family index frequency firstCurve finalCurve firstResidual finalResidual sourceDifference horizon
    horizonNonnegative firstContinuous finalContinuous firstForcingContinuous finalForcingContinuous actual
  have firstEquation (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      HasDerivAt (fun current => family.canonicalExteriorCommonQuadraticCoordinate index frequency current (firstCurve current))
        ((frequency • diskRotatingDerivative)
          (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (firstCurve time)) +
          family.canonicalExteriorCommonQuadraticMaterialForcing index frequency time (firstCurve time) (firstResidual time) 0) time := by
    obtain ⟨firstPhysical, _, firstSpectral, _, firstActual, _⟩ := actual time inside
    have transformed := evolution family index (firstResidual time) 0 firstPhysical firstSpectral
      (by simpa only [map_zero, add_zero] using firstActual)
    with_reducible_and_instances
      simpa only [canonicalExteriorCommonQuadraticMaterialForcing, ContinuousLinearMap.smul_apply, add_assoc] using transformed.2.1
  have finalEquation (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      HasDerivAt (fun current => family.canonicalExteriorCommonQuadraticCoordinate index frequency current (finalCurve current))
        ((frequency • diskRotatingDerivative)
          (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (finalCurve time)) +
          family.canonicalExteriorCommonQuadraticMaterialForcing index frequency time (finalCurve time)
            (finalResidual time) (sourceDifference time)) time := by
    obtain ⟨_, finalPhysical, _, finalSpectral, _, finalActual⟩ := actual time inside
    have transformed := evolution family index (finalResidual time) (sourceDifference time) finalPhysical finalSpectral finalActual
    with_reducible_and_instances
      simpa only [canonicalExteriorCommonQuadraticMaterialForcing, ContinuousLinearMap.smul_apply, add_assoc] using transformed.2.1
  have groupZero : diskPhysicalScaledGroup frequency 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    simpa only [diskPhysicalScaledGroup, mul_zero] using diskPhysicalGroup_zero
  have groupAddition (first final : ℝ) : diskPhysicalScaledGroup frequency (first + final) =
      (diskPhysicalScaledGroup frequency first).comp (diskPhysicalScaledGroup frequency final) := by
    simpa only [diskPhysicalScaledGroup, mul_add] using diskPhysicalGroup_add (frequency * first) (frequency * final)
  have history := EulerNonuniqueness.General.linearGroup_pair_history_of_interior
    (diskPhysicalScaledGroup frequency) (frequency • diskRotatingDerivative) groupZero groupAddition
    (diskPhysicalScaledGroup_generator frequency) diskPhysicalGroupBound_nonnegative
    (diskPhysicalScaledGroup_norm_bound frequency) horizonNonnegative firstContinuous finalContinuous
    firstForcingContinuous finalForcingContinuous firstEquation finalEquation
  intro time inside
  exact (history time inside).2

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
