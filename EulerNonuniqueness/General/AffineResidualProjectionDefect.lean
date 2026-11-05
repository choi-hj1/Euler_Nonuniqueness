import EulerNonuniqueness.General.AffineForcingResidualJet

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem affineResidual_projection_defect (generator forcingDerivative linear partner projection : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (value direction : Space) (frequency : ℝ)
    (homological : frequency • partner direction + linear (generator direction) - generator (linear direction) =
      forcingDerivative (projection direction) + second (projection direction) value) :
    (forcingDerivative + second.flip value + generator.comp linear - linear.comp generator - frequency • partner) direction =
      forcingDerivative (direction - projection direction) + second (direction - projection direction) value := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply]
  rw [forcingDerivative.map_sub, second.map_sub, ContinuousLinearMap.sub_apply]
  rw [show forcingDerivative direction + second direction value + generator (linear direction) -
      linear (generator direction) - frequency • partner direction =
    (forcingDerivative direction + second direction value) -
      (frequency • partner direction + linear (generator direction) - generator (linear direction)) by abel]
  rw [homological]
  abel

end EulerNonuniqueness.General
