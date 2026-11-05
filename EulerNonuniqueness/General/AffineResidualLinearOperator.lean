import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def affineResidualLinearOperator (sourceDerivative generator correction partnerCorrection : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (value : Space) : Space →L[ℝ] Space :=
  sourceDerivative + second.flip value + generator.comp correction - correction.comp generator - partnerCorrection

theorem affineResidualLinearOperator_apply (sourceDerivative generator correction partnerCorrection : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (value direction : Space) :
    affineResidualLinearOperator sourceDerivative generator correction partnerCorrection second value direction =
      sourceDerivative direction + second direction value + generator (correction direction) -
        correction (generator direction) - partnerCorrection direction := rfl

theorem affineResidualLinearOperator_norm_bound (sourceDerivative generator correction partnerCorrection : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (value : Space) :
    ‖affineResidualLinearOperator sourceDerivative generator correction partnerCorrection second value‖ ≤
      ‖sourceDerivative‖ + ‖second‖ * ‖value‖ + 2 * ‖generator‖ * ‖correction‖ + ‖partnerCorrection‖ := by
  have secondBound : ‖second.flip value‖ ≤ ‖second‖ * ‖value‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using second.flip.le_opNorm value
  unfold affineResidualLinearOperator
  calc
    _ ≤ ‖sourceDerivative + second.flip value + generator.comp correction‖ +
        ‖correction.comp generator‖ + ‖partnerCorrection‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ ‖sourceDerivative‖ + ‖second.flip value‖ + ‖generator.comp correction‖ +
        ‖correction.comp generator‖ + ‖partnerCorrection‖ := by
      gcongr
      exact norm_add₃_le
    _ ≤ ‖sourceDerivative‖ + ‖second‖ * ‖value‖ + ‖generator‖ * ‖correction‖ +
        ‖correction‖ * ‖generator‖ + ‖partnerCorrection‖ := by
      gcongr
      · exact ContinuousLinearMap.opNorm_comp_le _ _
      · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring

theorem affineResidualLinearOperator_apply_eq_zero
    (sourceDerivative generator correction partnerCorrection : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (value direction : Space)
    (equation : partnerCorrection direction + correction (generator direction) - generator (correction direction) =
      sourceDerivative direction + second direction value) :
    affineResidualLinearOperator sourceDerivative generator correction partnerCorrection second value direction = 0 := by
  rw [affineResidualLinearOperator_apply, ← equation]
  abel

end EulerNonuniqueness.General
