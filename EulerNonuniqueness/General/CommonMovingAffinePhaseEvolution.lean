import EulerNonuniqueness.General.CommonMovingAffineCoordinate

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem common_moving_affine_phase_evolution_hasDerivAt
    {curve base primitive : ℝ → Space} {correction : ℝ → Space →L[ℝ] Space}
    {time frequency : ℝ} (selfValue firstForce finalForce basePhase amplitudeError parameterPrimitive : Space)
    (phaseCorrection amplitudeCorrection parameterCorrection : Space →L[ℝ] Space)
    (baseVelocity : Space)
    (curveActual : HasDerivAt curve (frequency • selfValue + finalForce) time)
    (baseActual : HasDerivAt base baseVelocity time)
    (primitiveActual : HasDerivAt primitive (basePhase + amplitudeError + parameterPrimitive) time)
    (correctionActual : HasDerivAt correction
      (phaseCorrection + amplitudeCorrection + parameterCorrection) time) :
    HasDerivAt (fun current => curve current - primitive current -
      correction current (curve current - base current))
      ((frequency • selfValue + firstForce - correction time (frequency • selfValue + firstForce) -
          basePhase - phaseCorrection (curve time - base time)) -
        amplitudeError - amplitudeCorrection (curve time - base time) +
        (-parameterPrimitive - parameterCorrection (curve time - base time) + correction time baseVelocity) +
        (ContinuousLinearMap.id ℝ Space - correction time) (finalForce - firstForce)) time := by
  have actual := commonMovingAffineCoordinate_hasDerivAt curveActual baseActual primitiveActual correctionActual
  convert actual using 1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, map_add]
  abel

end EulerNonuniqueness.General
