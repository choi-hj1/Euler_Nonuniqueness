import EulerNonuniqueness.Section3.CanonicalExteriorCommonMovingEquation
import EulerNonuniqueness.Section3.CanonicalExteriorCommonNormalizedDerivative
import EulerNonuniqueness.General.CommonAngularSourceAlgebra

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

def canonicalExteriorCommonMaterialResidual {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time distance : ℝ) (positive : 0 < distance)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) (angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < 1 / 2) :
    PeriodicC1HolderHalf :=
  let angular := diskNeutralCLM (diskPhysicalSpectralCoordinate data)
  let force := family.canonicalProjectedExteriorContourField index time distance positive small separated
    (Circle.exp (frequency * time / 2))
  family.canonicalExteriorStaticPhaseResidual index angular frequency time distance positive small separated data -
    fixedRelabelEquivalence angular angularSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
    family.exteriorStrainAmplitudeCorrection index angular frequency time (data - diskRelabelCurve angular 1) +
    family.canonicalExteriorAffineAngularDerivative index angular frequency time data
      (diskNeutralCLM (diskPhysicalSpectralInverseDerivative data (frequency • diskEulerRotatingField data + force data)))

theorem canonicalExteriorCommonMaterialResidual_force_identity {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (frequency time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data finalForce : PeriodicC1HolderHalf)
    (angularSmall : ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < 1 / 2) :
    let angular := diskNeutralCLM (diskPhysicalSpectralCoordinate data)
    let force := family.canonicalProjectedExteriorContourField index time distance positive small separated
      (Circle.exp (frequency * time / 2))
    family.canonicalExteriorAffinePhaseField index angular frequency time distance positive small separated data -
        fixedRelabelEquivalence angular angularSmall (family.exteriorAmplitudeDerivativePrimitive index frequency time) -
        family.exteriorStrainAmplitudeCorrection index angular frequency time (data - diskRelabelCurve angular 1) +
        family.canonicalExteriorAffineAngularDerivative index angular frequency time data
          (diskNeutralCLM (diskPhysicalSpectralInverseDerivative data (frequency • diskEulerRotatingField data + finalForce))) +
        (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf - family.exteriorStrainPhysicalCorrection index angular frequency time)
          (finalForce - force data) =
      frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time data) +
        family.canonicalExteriorCommonMaterialResidual index frequency time distance positive small separated data angularSmall +
        family.canonicalExteriorCommonPhysicalDerivative index frequency time data (finalForce - force data) := by
  simp only [canonicalExteriorCommonMaterialResidual, canonicalExteriorStaticPhaseResidual,
    canonicalExteriorCommonPhysicalCoordinate, canonicalExteriorCommonPhysicalDerivative,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel

theorem canonicalExteriorCommonNormalizedPhysicalCoordinate_exists_material_evolution_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        {curve : ℝ → PeriodicC1HolderHalf} {frequency time : ℝ}
        (residual sourceDifference : PeriodicC1HolderHalf),
      ‖family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time) - standardCircleBanach‖ ≤ radius →
      HasDerivAt (fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
        (frequency • diskEulerRotatingField (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) +
          residual + family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time) sourceDifference) time →
      diskSpectralTubularArea (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)) = Real.pi ∧
      HasDerivAt (fun current => family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency current (curve current))
        (frequency • diskSpectralTubularEulerField
            (family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (curve time)) +
          diskNormalizedSpectralError
            (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual +
          family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time (curve time) sourceDifference) time ∧
      ‖diskNormalizedSpectralError (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual‖ ≤
        constant * ‖residual‖ := by
  obtain ⟨radius, positive, constant, one, evolution⟩ := diskNormalizedSpectralCoordinate_exists_uniform_evolution
  refine ⟨radius, positive, constant, one, ?_⟩
  intro count family index curve frequency time residual sourceDifference nearby actual
  have actualEvolution := evolution
    (curve := fun current => family.canonicalExteriorCommonPhysicalCoordinate index frequency current (curve current))
    (time := time) (frequency := frequency)
    (error := residual + family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time) sourceDifference)
    nearby (by
    simpa only [add_assoc] using actual)
  have linear : diskNormalizedSpectralError
      (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time))
      (residual + family.canonicalExteriorCommonPhysicalDerivative index frequency time (curve time) sourceDifference) =
      diskNormalizedSpectralError (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time)) residual +
        family.canonicalExteriorCommonNormalizedPhysicalDerivative index frequency time (curve time) sourceDifference := by
    simp only [diskNormalizedSpectralError, canonicalExteriorCommonNormalizedPhysicalDerivative,
      ContinuousLinearMap.comp_apply, map_add]
  have residualBound := evolution (curve := fun current : ℝ =>
    family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time) + current • residual)
    (time := 0) (frequency := 0) (error := residual) (by simpa using nearby)
    (by
      have auxiliary := (hasDerivAt_const (0 : ℝ)
        (family.canonicalExteriorCommonPhysicalCoordinate index frequency time (curve time))).add
          ((hasDerivAt_id (0 : ℝ)).smul_const residual)
      simpa using auxiliary)
  refine ⟨actualEvolution.1, ?_, ?_⟩
  · simpa only [canonicalExteriorCommonNormalizedPhysicalCoordinate, linear, add_assoc] using actualEvolution.2.1
  · simpa using residualBound.2.2

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
