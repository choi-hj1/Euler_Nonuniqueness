import EulerNonuniqueness.General.OperatorProjectionFiber

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem spectralTubularChart_fderiv_fiber_apply
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral relative direction : Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral) (relativeKernel : projection relative = 0)
    (regular : DifferentiableAt ℝ operator neutral)
    (fixes : (operator neutral).comp projection = projection) :
    fderiv ℝ (spectralTubularChart projection operator) (neutral + relative) direction =
      operator neutral direction + fderiv ℝ operator neutral direction relative := by
  have actual := spectralTubularChart_hasFDerivAt_fiber_of_differentiable projection operator
    neutral relative factors neutralFixed relativeKernel regular fixes
  rw [actual.fderiv]
  rfl

end EulerNonuniqueness.General
