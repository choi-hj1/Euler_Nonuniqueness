import EulerNonuniqueness.General.SpectralTubularChart

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem operator_derivative_factors_projection
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral : Space) (differential : Space →L[ℝ] Space →L[ℝ] Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral)
    (actual : HasFDerivAt operator differential neutral) : differential.comp projection = differential := by
  have atImage : HasFDerivAt operator differential (projection neutral) := by rw [neutralFixed]; exact actual
  have composed := atImage.comp neutral (projection.hasFDerivAt (x := neutral))
  have identity : (fun value => operator (projection value)) = operator := funext factors
  change HasFDerivAt (fun value => operator (projection value)) (differential.comp projection) neutral at composed
  rw [identity] at composed
  exact composed.unique actual

theorem operator_hasFDerivAt_on_projection_fiber
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral relative : Space) (differential : Space →L[ℝ] Space →L[ℝ] Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral) (relativeKernel : projection relative = 0)
    (actual : HasFDerivAt operator differential neutral) :
    HasFDerivAt operator differential (neutral + relative) := by
  have member : projection (neutral + relative) = neutral := by rw [map_add, neutralFixed, relativeKernel, add_zero]
  have atImage : HasFDerivAt operator differential (projection (neutral + relative)) := by rw [member]; exact actual
  have composed := atImage.comp (neutral + relative) (projection.hasFDerivAt (x := neutral + relative))
  have identity : (fun value => operator (projection value)) = operator := funext factors
  change HasFDerivAt (fun value => operator (projection value)) (differential.comp projection) (neutral + relative) at composed
  rw [identity, operator_derivative_factors_projection projection operator neutral differential factors neutralFixed actual] at composed
  exact composed

theorem fderiv_operator_zero_on_projection_kernel
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral direction : Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral) (directionKernel : projection direction = 0)
    (regular : DifferentiableAt ℝ operator neutral) : fderiv ℝ operator neutral direction = 0 := by
  have identity := operator_derivative_factors_projection projection operator neutral
    (fderiv ℝ operator neutral) factors neutralFixed regular.hasFDerivAt
  have evaluated := congrArg (fun linear : Space →L[ℝ] Space →L[ℝ] Space => linear direction) identity
  change fderiv ℝ operator neutral (projection direction) = fderiv ℝ operator neutral direction at evaluated
  rw [directionKernel, map_zero] at evaluated
  exact evaluated.symm

theorem spectralTubularChart_fiber
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral relative : Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral) (relativeKernel : projection relative = 0) :
    spectralTubularChart projection operator (neutral + relative) = neutral + operator neutral relative := by
  have member : projection (neutral + relative) = neutral := by rw [map_add, neutralFixed, relativeKernel, add_zero]
  have coefficient : operator (neutral + relative) = operator neutral := by
    rw [← factors (neutral + relative), member]
  simp only [spectralTubularChart, member, coefficient, add_sub_cancel_left]

theorem spectralTubularChart_hasFDerivAt_fiber
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral relative : Space) (differential : Space →L[ℝ] Space →L[ℝ] Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral) (relativeKernel : projection relative = 0)
    (actual : HasFDerivAt operator differential neutral)
    (fixes : (operator neutral).comp projection = projection) :
    HasFDerivAt (spectralTubularChart projection operator)
      (operator neutral + differential.flip relative) (neutral + relative) := by
  have member : projection (neutral + relative) = neutral := by rw [map_add, neutralFixed, relativeKernel, add_zero]
  have coefficient : operator (neutral + relative) = operator neutral := by rw [← factors (neutral + relative), member]
  have fiberActual := operator_hasFDerivAt_on_projection_fiber projection operator neutral relative differential
    factors neutralFixed relativeKernel actual
  have difference := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Space) (F := Space)
    (ContinuousLinearMap.id ℝ Space - projection) (x := neutral + relative)
  have paired := fiberActual.clm_apply difference
  have result := (projection.hasFDerivAt (x := neutral + relative)).add paired
  have relativeIdentity : (ContinuousLinearMap.id ℝ Space - projection) (neutral + relative) = relative := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, member, add_sub_cancel_left]
  rw [coefficient, relativeIdentity] at result
  have derivativeIdentity : projection + ((operator neutral).comp (ContinuousLinearMap.id ℝ Space - projection) +
      differential.flip relative) = operator neutral + differential.flip relative := by
    apply ContinuousLinearMap.ext
    intro direction
    have fixed := congrArg (fun linear : Space →L[ℝ] Space => linear direction) fixes
    change projection direction + (operator neutral (direction - projection direction) + differential direction relative) = _
    change operator neutral (projection direction) = projection direction at fixed
    rw [map_sub, fixed]
    change projection direction + (operator neutral direction - projection direction + differential direction relative) =
      operator neutral direction + differential direction relative
    abel
  rw [derivativeIdentity] at result
  exact result

theorem spectralTubularChart_hasFDerivAt_fiber_of_differentiable
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (neutral relative : Space)
    (factors : ∀ value, operator (projection value) = operator value)
    (neutralFixed : projection neutral = neutral) (relativeKernel : projection relative = 0)
    (regular : DifferentiableAt ℝ operator neutral)
    (fixes : (operator neutral).comp projection = projection) :
    HasFDerivAt (spectralTubularChart projection operator)
      (operator neutral + (fderiv ℝ operator neutral).flip relative) (neutral + relative) :=
  spectralTubularChart_hasFDerivAt_fiber projection operator neutral relative
    (fderiv ℝ operator neutral) factors neutralFixed relativeKernel regular.hasFDerivAt fixes

end EulerNonuniqueness.General
