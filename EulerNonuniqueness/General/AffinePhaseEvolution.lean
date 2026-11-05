import EulerNonuniqueness.General.PhysicalAffineForcingTransform

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem affine_phase_evolution_hasDerivAt
    {curve primitive : ℝ → Space} {correction : ℝ → Space →L[ℝ] Space}
    {time frequency : ℝ} (base selfValue forceValue basePhase amplitudeError : Space)
    (phaseCorrection amplitudeCorrection : Space →L[ℝ] Space)
    (curveActual : HasDerivAt curve (frequency • selfValue + forceValue) time)
    (primitiveActual : HasDerivAt primitive (basePhase + amplitudeError) time)
    (correctionActual : HasDerivAt correction (phaseCorrection + amplitudeCorrection) time) :
    HasDerivAt (fun current => curve current - primitive current - correction current (curve current - base))
      (frequency • selfValue + forceValue - correction time (frequency • selfValue + forceValue) -
        basePhase - phaseCorrection (curve time - base) - amplitudeError - amplitudeCorrection (curve time - base)) time := by
  have actual := physical_affine_forcing_transform_hasDerivAt base
    (frequency • selfValue + forceValue) (basePhase + amplitudeError)
    (phaseCorrection + amplitudeCorrection) curveActual primitiveActual correctionActual
  have velocityIdentity :
      frequency • selfValue + forceValue - (basePhase + amplitudeError) -
        (correction time (frequency • selfValue + forceValue) +
          (phaseCorrection + amplitudeCorrection) (curve time - base)) =
      frequency • selfValue + forceValue - correction time (frequency • selfValue + forceValue) -
        basePhase - phaseCorrection (curve time - base) - amplitudeError - amplitudeCorrection (curve time - base) := by
    rw [ContinuousLinearMap.add_apply]
    abel
  rwa [velocityIdentity] at actual

end EulerNonuniqueness.General
