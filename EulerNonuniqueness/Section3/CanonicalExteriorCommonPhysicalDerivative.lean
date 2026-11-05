import EulerNonuniqueness.Section3.CanonicalExteriorAngularParameterDerivative
import EulerNonuniqueness.Section3.DiskPhysicalSpectralEquation

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  powerFirstJetOperatorGroup exteriorPowerSeriesOperatorSpace gaugeOperatorUniformSecondGroup
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

def canonicalExteriorCommonPhysicalCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  family.canonicalExteriorAffineCoordinate index (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) frequency time data

def canonicalExteriorCommonPhysicalDerivative {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  ContinuousLinearMap.id ℝ PeriodicC1HolderHalf -
    family.exteriorStrainPhysicalCorrection index (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) frequency time +
    (family.canonicalExteriorAffineAngularDerivative index
      (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) frequency time data).comp
      (diskNeutralCLM.comp (diskPhysicalSpectralInverseDerivative data))

theorem canonicalExteriorCommonPhysicalCoordinate_hasFDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    {frequency time : ℝ} (nonzero : frequency ≠ 0) (data : PeriodicC1HolderHalf)
    (inverseActual : HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative data) data)
    (bounded : ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1‖ < 3)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) *
      ‖family.canonicalExteriorStaticCoefficient index time degree‖))
    (regular : DifferentiableAt ℝ movingStrainAngularCoefficient
      (diskNeutralCLM (diskPhysicalSpectralCoordinate data))) :
    HasFDerivAt (family.canonicalExteriorCommonPhysicalCoordinate index frequency time)
      (family.canonicalExteriorCommonPhysicalDerivative index frequency time data) data := by
  let angular := diskNeutralCLM (diskPhysicalSpectralCoordinate data)
  have angularActual := diskNeutralCLM.hasFDerivAt.comp data inverseActual
  have baseActual := (diskRelabelMap_analyticAt angular).differentiableAt.hasFDerivAt.comp data angularActual
  have primitiveActual := (relabeledForcingPrimitiveSeries_hasFDerivAt_angular nonzero
    (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (degree + 1)) time angular bounded weighted).comp data angularActual
  have correctionActual := (family.exteriorStrainPhysicalCorrection_hasFDerivAt_angular
    index angular frequency time regular).comp data angularActual
  have actual := EulerNonuniqueness.General.commonMovingAffineCoordinate_hasFDerivAt
    baseActual primitiveActual correctionActual
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    all_goals first
      | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
      | (funext current
         simp only [EulerNonuniqueness.General.commonMovingAffineCoordinate,
           canonicalExteriorCommonPhysicalCoordinate, canonicalExteriorAffineCoordinate,
           relabeledExteriorForcingPrimitive, Function.comp_def])
      | (apply ContinuousLinearMap.ext
         intro direction
         simp only [canonicalExteriorCommonPhysicalDerivative,
           EulerNonuniqueness.General.commonMovingAffineDerivative,
           canonicalExteriorAffineAngularDerivative_apply, ContinuousLinearMap.add_apply,
           ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
           ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
           ContinuousLinearMap.flip_apply, Function.comp_def, angular]
         rw [(family.exteriorStrainPhysicalCorrection index angular frequency time).map_sub]
         abel)

theorem canonicalExteriorCommonPhysicalDerivative_source_difference {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (frequency time : ℝ) (data commonTimeDerivative firstForce finalForce : PeriodicC1HolderHalf) :
    (commonTimeDerivative + family.canonicalExteriorCommonPhysicalDerivative index frequency time data
        (frequency • diskEulerRotatingField data + finalForce)) -
      (commonTimeDerivative + family.canonicalExteriorCommonPhysicalDerivative index frequency time data
        (frequency • diskEulerRotatingField data + firstForce)) =
    family.canonicalExteriorCommonPhysicalDerivative index frequency time data (finalForce - firstForce) := by
  simp only [map_add, map_sub]
  abel

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
