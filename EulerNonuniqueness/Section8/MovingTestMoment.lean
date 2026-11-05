import EulerNonuniqueness.General.StrongL1MovingPairing
import EulerNonuniqueness.Section8.CompactnessStatement
import EulerNonuniqueness.Section8.TestBounds

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem ContinuousInLpOn.continuousOn_moving_test_moment
    {horizon : ℝ} {omega : Evolution} (continuous : ContinuousInLpOn horizon 1 omega)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ContinuousOn (fun time => ∫ position, omega time position * test (time, position)) (Icc 0 horizon) := by
  obtain ⟨exponentBound, members, quotientContinuous⟩ := continuous
  obtain ⟨bound, nonnegative, bounded⟩ := scalarTest_uniform_bounds smooth compact
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_integral_mul_of_continuous_L1 members quotientContinuous
  · intro time
    exact (contDiff_spatial_slice smooth time).continuous.measurable
  · intro position
    exact smooth.continuous.comp (continuous_subtype_val.prodMk continuous_const)
  · intro time position
    exact (bounded time position).1

end EulerNonuniqueness
