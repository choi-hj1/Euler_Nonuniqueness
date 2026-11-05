import EulerNonuniqueness.Section6.PhaseStraightening
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem shapeChartAngle_forced_hasDerivAt {trajectory : ℝ → ℝ × ℝ}
    {frequency time : ℝ} {forcing : ℝ × ℝ}
    (equation : HasDerivAt trajectory (shapeChartVelocity frequency (trajectory time) + forcing) time) :
    HasDerivAt (fun current => shapeChartAngle (trajectory current))
      (shapeAngleVelocity frequency (shapeChartRatio (trajectory time)) (shapeChartAngle (trajectory time)) +
        Real.sqrt 2 * (forcing.1 - forcing.2)) time := by
  have first := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time equation
  have second := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time equation
  have actual := ((first.sub second).const_mul (Real.sqrt 2)).const_add Real.pi
  convert actual using 1
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add]
  unfold shapeChartVelocity
  field_simp
  ring

theorem adjustedPhase_forced_hasDerivAt {phase : ℝ → ℝ} {trajectory : ℝ → ℝ × ℝ}
    {frequency time phaseForcing : ℝ} {forcing : ℝ × ℝ}
    (equation : HasDerivAt trajectory (shapeChartVelocity frequency (trajectory time) + forcing) time)
    (phaseEquation : HasDerivAt phase
      (rotationVelocity frequency (shapeChartRatio (trajectory time)) (shapeChartAngle (trajectory time)) + phaseForcing) time) :
    HasDerivAt (fun current => phase current - (Real.sqrt 2 - 1) / 4 * shapeChartAngle (trajectory current))
      (-frequency + adjustedPhaseError frequency (trajectory time) + phaseForcing -
        (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 * (forcing.1 - forcing.2)) time := by
  have actual := phaseEquation.sub ((shapeChartAngle_forced_hasDerivAt equation).const_mul ((Real.sqrt 2 - 1) / 4))
  convert actual using 1
  dsimp only [adjustedPhaseError, rawAdjustedPhaseError]
  ring

theorem adjustedPhaseError_frequency_mul (frequency : ℝ) (point : ℝ × ℝ) :
    adjustedPhaseError frequency point = frequency * adjustedPhaseError 1 point := by
  unfold adjustedPhaseError rawAdjustedPhaseError rotationVelocity shapeAngleVelocity
  ring

theorem correctedPhaseError_frequency_mul (frequency : ℝ) (correction : ℝ → ℝ) (point : ℝ × ℝ) :
    correctedPhaseError frequency correction point = frequency * correctedPhaseError 1 correction point := by
  rw [correctedPhaseError, adjustedPhaseError_frequency_mul, shapeChartVelocity_frequency_smul]
  simp only [Prod.smul_fst, smul_eq_mul, correctedPhaseError]
  ring

end EulerNonuniqueness.Section6
