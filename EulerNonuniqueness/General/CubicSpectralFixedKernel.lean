import EulerNonuniqueness.General.CubicSpectralIntertwiner

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem cubicSpectralIntertwiner_fixed_of_common_kernel
    (operator reference : Space →L[ℝ] Space) (value : Space)
    (operatorKernel : operator value = 0) (referenceKernel : reference value = 0) :
    cubicSpectralIntertwiner operator reference value = value := by
  simp only [cubicSpectralIntertwiner, cubicSpectralProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, referenceKernel, operatorKernel, map_zero, smul_zero,
    sub_zero, map_sub, zero_add, add_zero]

end EulerNonuniqueness.General
