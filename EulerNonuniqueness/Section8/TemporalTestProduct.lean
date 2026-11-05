import EulerNonuniqueness.Section8.TestSlices
import EulerNonuniqueness.General.TerminalCutoff

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace EulerNonuniqueness

def temporalTestProduct (temporal : ℝ → ℝ) (test : ℝ × Plane → ℝ) (point : ℝ × Plane) : ℝ :=
  temporal point.1 * test point

theorem contDiff_temporalTestProduct {temporal : ℝ → ℝ} {test : ℝ × Plane → ℝ}
    (temporalSmooth : ContDiff ℝ ∞ temporal) (smooth : ContDiff ℝ ∞ test) :
    ContDiff ℝ ∞ (temporalTestProduct temporal test) :=
  (temporalSmooth.comp contDiff_fst).mul smooth

theorem hasCompactSupport_temporalTestProduct (temporal : ℝ → ℝ) {test : ℝ × Plane → ℝ}
    (compact : HasCompactSupport test) : HasCompactSupport (temporalTestProduct temporal test) := compact.mul_left

theorem timeDerivative_temporalTestProduct {temporal : ℝ → ℝ} {test : ℝ × Plane → ℝ}
    (temporalSmooth : ContDiff ℝ ∞ temporal) (smooth : ContDiff ℝ ∞ test) (point : ℝ × Plane) :
    timeDerivative (temporalTestProduct temporal test) point =
      deriv temporal point.1 * test point + temporal point.1 * timeDerivative test point := by
  rw [← deriv_temporal_slice (contDiff_temporalTestProduct temporalSmooth smooth) point.1 point.2]
  exact ((temporalSmooth.differentiable (by simp) point.1).hasDerivAt.mul
    (hasDerivAt_temporal_slice smooth point.1 point.2)).deriv

theorem spatialDerivative_temporalTestProduct {temporal : ℝ → ℝ} {test : ℝ × Plane → ℝ}
    (temporalSmooth : ContDiff ℝ ∞ temporal) (smooth : ContDiff ℝ ∞ test)
    (point : ℝ × Plane) (direction : Plane) :
    spatialDerivative (temporalTestProduct temporal test) point direction =
      temporal point.1 * spatialDerivative test point direction := by
  rw [← fderiv_spatial_slice (contDiff_temporalTestProduct temporalSmooth smooth) point.1 point.2 direction]
  have derivative := ((contDiff_spatial_slice smooth point.1).differentiable (by simp) point.2).hasFDerivAt.const_mul (temporal point.1)
  change fderiv ℝ (fun position => temporal point.1 * test (point.1, position)) point.2 direction = _
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_spatial_slice smooth]

theorem scalarTestOn_terminalCutoff_product {horizon : ℝ} (positive : 0 < horizon) (index : ℕ)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ScalarTestOn horizon (temporalTestProduct (terminalCutoff horizon index) test) := by
  refine ⟨contDiff_temporalTestProduct (contDiff_terminalCutoff horizon index) smooth,
    hasCompactSupport_temporalTestProduct _ compact, ?_⟩
  intro time position after
  change terminalCutoff horizon index time * test (time, position) = 0
  rw [terminalCutoff_eq_zero_after positive index after, zero_mul]

end EulerNonuniqueness
