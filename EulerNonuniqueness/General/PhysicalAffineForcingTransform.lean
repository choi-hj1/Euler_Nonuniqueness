import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem physical_affine_forcing_transform_residual_identity
    (frequency : ℝ)
    (selfValue correctedSelfValue forceValue leadingForceValue baseForceValue baseLeadingForceValue : Space)
    (primitive leadingPrimitive primitivePhase leadingPrimitivePhase primitiveAmplitude relative : Space)
    (generator baseGenerator correction phaseCorrection amplitudeCorrection : Space →L[ℝ] Space)
    (phaseEquation : primitivePhase = leadingPrimitivePhase +
      frequency • baseGenerator (primitive - leadingPrimitive) + (baseForceValue - baseLeadingForceValue)) :
    frequency • selfValue + forceValue - correction (frequency • selfValue + forceValue) -
        primitivePhase - phaseCorrection relative - primitiveAmplitude - amplitudeCorrection relative -
        frequency • correctedSelfValue =
      frequency • (selfValue - generator (primitive + correction relative) - correctedSelfValue) +
        (leadingForceValue + frequency • generator (leadingPrimitive + correction relative) -
          correction (frequency • selfValue) - leadingPrimitivePhase - phaseCorrection relative) +
        ((forceValue - leadingForceValue) - (baseForceValue - baseLeadingForceValue) +
          frequency • ((generator - baseGenerator) (primitive - leadingPrimitive))) -
        correction forceValue - primitiveAmplitude - amplitudeCorrection relative := by
  rw [phaseEquation]
  simp only [map_add, map_sub, ContinuousLinearMap.sub_apply, smul_add, smul_sub]
  abel

theorem physical_affine_forcing_transform_hasDerivAt
    {curve primitive : ℝ → Space} {correction : ℝ → Space →L[ℝ] Space}
    {time : ℝ} (base curveVelocity primitiveVelocity : Space) (correctionVelocity : Space →L[ℝ] Space)
    (curveActual : HasDerivAt curve curveVelocity time)
    (primitiveActual : HasDerivAt primitive primitiveVelocity time)
    (correctionActual : HasDerivAt correction correctionVelocity time) :
    HasDerivAt (fun current => curve current - primitive current - correction current (curve current - base))
      (curveVelocity - primitiveVelocity -
        (correction time curveVelocity + correctionVelocity (curve time - base))) time := by
  have paired := correctionActual.clm_apply (curveActual.sub_const base)
  simpa only [add_comm] using (curveActual.sub primitiveActual).sub paired

end EulerNonuniqueness.General
