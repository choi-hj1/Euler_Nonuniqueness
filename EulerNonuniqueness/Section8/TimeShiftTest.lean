import EulerNonuniqueness.Definitions

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace EulerNonuniqueness

def timeShiftTest (shift : ℝ) (test : ℝ × Plane → ℝ) (point : ℝ × Plane) : ℝ :=
  test ((shift, 0) + point)

theorem contDiff_timeShiftTest {test : ℝ × Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (shift : ℝ) : ContDiff ℝ ∞ (timeShiftTest shift test) :=
  smooth.comp (contDiff_const.add contDiff_id)

theorem hasCompactSupport_timeShiftTest {test : ℝ × Plane → ℝ}
    (compact : HasCompactSupport test) (shift : ℝ) : HasCompactSupport (timeShiftTest shift test) := by
  simpa [timeShiftTest, Function.comp_def, Homeomorph.addLeft] using
    compact.comp_homeomorph (Homeomorph.addLeft (shift, (0 : Plane)))

theorem timeDerivative_timeShiftTest {test : ℝ × Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (shift : ℝ) (point : ℝ × Plane) :
    timeDerivative (timeShiftTest shift test) point = timeDerivative test (shift + point.1, point.2) := by
  have derivative := ((smooth.differentiable (by simp)) ((shift, (0 : Plane)) + point)).hasFDerivAt.comp point
    ((hasFDerivAt_const (shift, (0 : Plane)) point).add (hasFDerivAt_id point))
  change fderiv ℝ (test ∘ HAdd.hAdd (shift, (0 : Plane))) point (1, 0) = _
  rw [derivative.fderiv]
  simp [timeDerivative, ContinuousLinearMap.comp_apply, Prod.add_def]

theorem spatialDerivative_timeShiftTest {test : ℝ × Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (shift : ℝ) (point : ℝ × Plane) (direction : Plane) :
    spatialDerivative (timeShiftTest shift test) point direction =
      spatialDerivative test (shift + point.1, point.2) direction := by
  have derivative := ((smooth.differentiable (by simp)) ((shift, (0 : Plane)) + point)).hasFDerivAt.comp point
    ((hasFDerivAt_const (shift, (0 : Plane)) point).add (hasFDerivAt_id point))
  change fderiv ℝ (test ∘ HAdd.hAdd (shift, (0 : Plane))) point (0, direction) = _
  rw [derivative.fderiv]
  simp [spatialDerivative, ContinuousLinearMap.comp_apply, Prod.add_def]

theorem scalarTestOn_timeShiftTest {first second : ℝ} {test : ℝ × Plane → ℝ}
    (admissible : ScalarTestOn (first + second) test) : ScalarTestOn second (timeShiftTest first test) := by
  refine ⟨contDiff_timeShiftTest admissible.1 first, hasCompactSupport_timeShiftTest admissible.2.1 first, ?_⟩
  intro time position inside
  simpa [timeShiftTest] using admissible.2.2 (first + time) position (by linarith)

end EulerNonuniqueness
