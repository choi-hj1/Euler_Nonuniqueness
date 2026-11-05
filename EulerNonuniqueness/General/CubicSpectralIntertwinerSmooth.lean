import EulerNonuniqueness.General.CubicSpectralIntertwinerRegularity

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem cubicSpectralIntertwiner_contDiff (reference : Space →L[ℝ] Space) (order : ℕ∞) :
    ContDiff ℝ order (fun operator : Space →L[ℝ] Space => cubicSpectralIntertwiner operator reference) := by
  unfold cubicSpectralIntertwiner cubicSpectralProjection
  have identity : ContDiff ℝ order (fun operator : Space →L[ℝ] Space => operator) := contDiff_id
  have projection := (identity.clm_comp identity).const_smul (-4 : ℝ)
  exact (((contDiff_const.sub projection).clm_comp contDiff_const).add
    ((projection.clm_comp contDiff_const).const_smul (1 / 2 : ℝ))).sub
      ((identity.clm_comp contDiff_const).const_smul (2 : ℝ))

end EulerNonuniqueness.General
