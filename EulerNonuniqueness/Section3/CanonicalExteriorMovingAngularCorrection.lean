import EulerNonuniqueness.Section3.CanonicalExteriorAngularParameterDerivative
import EulerNonuniqueness.Section3.CanonicalExteriorAffineDerivative

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

theorem exteriorStrainPhysicalCorrection_hasDerivAt_moving_angular_material {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    {angular : ℝ → PeriodicC1HolderHalf} {angularVelocity : PeriodicC1HolderHalf}
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0)
    (angularActual : HasDerivAt angular angularVelocity time)
    (regular : DifferentiableAt ℝ movingStrainAngularCoefficient (angular time))
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ Finset.univ.erase index, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (positive : 0 < distance)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    HasDerivAt (fun current => family.exteriorStrainPhysicalCorrection index (angular current) frequency current)
      (movingStrainRealCorrectionCLM (diskRelabelCurve (angular time) 1)
          (-Complex.I * family.exteriorStrainModulatedCoefficient index frequency time) +
        family.exteriorStrainAmplitudeCorrection index (angular time) frequency time +
        frequency⁻¹ • movingStrainAngularCorrectionDerivative (angular time)
          (family.exteriorStrainModulatedCoefficient index frequency time) angularVelocity) time := by
  have amplitudeActual := family.exteriorTaylorCoefficient_hasDerivAt_material index 0 inside material positive centerGaps
  have coefficientActual := diskStrainModulatedCoefficient_hasDerivAt frequency time amplitudeActual
  have angularCoefficientActual := regular.hasFDerivAt.comp_hasDerivAt time angularActual
  have actual := (angularCoefficientActual.clm_apply coefficientActual).const_smul frequency⁻¹
  have cast (value : ℂ) : (frequency : ℂ) * value = frequency • value := rfl
  rw [cast] at actual
  simp only [map_add, map_smul, smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul] at actual
  have coefficientApplication (currentAngular : PeriodicC1HolderHalf) (value : ℂ) :
      movingStrainAngularCoefficient currentAngular value =
      movingStrainRealCorrectionCLM (diskRelabelCurve currentAngular 1) value :=
    movingStrainCorrectionCoefficient_apply _ _
  have angularDerivativeIdentity (value : ℂ) :
      (fderiv ℝ movingStrainAngularCoefficient (angular time) angularVelocity)
        value =
      movingStrainAngularCorrectionDerivative (angular time)
        value angularVelocity := rfl
  unfold exteriorStrainPhysicalCorrection exteriorStrainAmplitudeCorrection exteriorStrainModulatedCoefficient
  simp only [Function.comp_def, coefficientApplication, angularDerivativeIdentity] at actual
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    all_goals first
      | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
      | rfl
      | (funext current
         simp only [Function.comp_def, movingStrainAngularCoefficient,
           movingStrainCorrectionCoefficient_apply])
      | abel

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
