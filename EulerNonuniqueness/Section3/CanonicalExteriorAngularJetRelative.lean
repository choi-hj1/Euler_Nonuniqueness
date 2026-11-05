import EulerNonuniqueness.Section3.CanonicalExteriorAngularParameterDerivative
import EulerNonuniqueness.General.MovingAffineAngularJetRelative

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem canonicalExteriorAffineAngularDerivative_relative_bound {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (firstAngular finalAngular firstData finalData : PeriodicC1HolderHalf) (frequency time : ℝ) :
    let primitive := fun angular => relabeledPrimitiveAngularDerivative frequency
      (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time angular
    let correctionDerivative := fun angular => frequency⁻¹ • movingStrainAngularCorrectionDerivative angular
      (family.exteriorStrainModulatedCoefficient index frequency time)
    let correction := fun angular => family.exteriorStrainPhysicalCorrection index angular frequency time
    let baseDerivative := fun angular => fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) angular
    ‖family.canonicalExteriorAffineAngularDerivative index firstAngular frequency time firstData -
      family.canonicalExteriorAffineAngularDerivative index finalAngular frequency time finalData‖ ≤
      ‖primitive firstAngular - primitive finalAngular‖ +
      (‖correctionDerivative firstAngular‖ *
          ‖(firstData - diskRelabelCurve firstAngular 1) - (finalData - diskRelabelCurve finalAngular 1)‖ +
        ‖correctionDerivative firstAngular - correctionDerivative finalAngular‖ *
          ‖finalData - diskRelabelCurve finalAngular 1‖) +
      (‖correction firstAngular‖ * ‖baseDerivative firstAngular - baseDerivative finalAngular‖ +
        ‖correction firstAngular - correction finalAngular‖ * ‖baseDerivative finalAngular‖) := by
  let firstBaseDerivative := fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) firstAngular
  let finalBaseDerivative := fderiv ℝ (fun parameter => diskRelabelCurve parameter 1) finalAngular
  have actual := EulerNonuniqueness.General.movingAffineAngularJet_relative_bound
        (relabeledPrimitiveAngularDerivative frequency
          (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time firstAngular)
        (relabeledPrimitiveAngularDerivative frequency
          (fun degree current => family.canonicalExteriorStaticCoefficient index current degree) time finalAngular)
        (family.exteriorStrainPhysicalCorrection index firstAngular frequency time)
        (family.exteriorStrainPhysicalCorrection index finalAngular frequency time)
        firstBaseDerivative finalBaseDerivative
        (frequency⁻¹ • movingStrainAngularCorrectionDerivative firstAngular
          (family.exteriorStrainModulatedCoefficient index frequency time))
        (frequency⁻¹ • movingStrainAngularCorrectionDerivative finalAngular
          (family.exteriorStrainModulatedCoefficient index frequency time))
        (firstData - diskRelabelCurve firstAngular 1) (finalData - diskRelabelCurve finalAngular 1)
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    all_goals first
      | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
      | (simp only [canonicalExteriorAffineAngularDerivative, canonicalExteriorStaticCoefficient,
          firstBaseDerivative, finalBaseDerivative])
      | rfl

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
