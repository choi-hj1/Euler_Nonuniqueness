import EulerNonuniqueness.Section3.DiskPhysicalGenerator
import EulerNonuniqueness.General.LinearGroupDuhamel
import EulerNonuniqueness.General.LinearGroupRate

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] physicalGeneratorC1Space physicalGeneratorC1BoundedSMul
  physicalGeneratorC1ContinuousAdd physicalGeneratorC1UniformAdd
  physicalGeneratorOperatorGroup physicalGeneratorOperatorSpace

def diskPhysicalRateGroup (frequency time : ℝ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskPhysicalGroup (frequency * time)

theorem diskPhysicalRateGroup_zero (frequency : ℝ) :
    diskPhysicalRateGroup frequency 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  simpa only [diskPhysicalRateGroup, mul_zero] using diskPhysicalGroup_zero

theorem diskPhysicalRateGroup_add (frequency first second : ℝ) :
    diskPhysicalRateGroup frequency (first + second) =
      (diskPhysicalRateGroup frequency first).comp (diskPhysicalRateGroup frequency second) := by
  simpa only [diskPhysicalRateGroup, mul_add] using diskPhysicalGroup_add (frequency * first) (frequency * second)

theorem diskPhysicalRateGroup_hasDerivAt (frequency time : ℝ) :
    HasDerivAt (diskPhysicalRateGroup frequency)
      ((diskPhysicalRateGroup frequency time).comp (frequency • diskRotatingDerivative)) time := by
  unfold diskPhysicalRateGroup
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_rate_hasDerivAt (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup diskRotatingDerivative
      diskPhysicalGroup_generator frequency time

theorem diskPhysicalRateGroup_norm_bound (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    ‖diskPhysicalRateGroup frequency time data‖ ≤ diskPhysicalGroupBound * ‖data‖ :=
  diskPhysicalGroup_norm_bound (frequency * time) data

theorem diskPhysicalRateGroup_response_bound
    {trajectory forcing : ℝ → PeriodicC1HolderHalf} {horizon time : ℝ} (frequency : ℝ)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt trajectory ((frequency • diskRotatingDerivative) (trajectory current) + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖trajectory time‖ ≤ diskPhysicalGroupBound *
      (‖trajectory 0‖ + ∫ current in (0 : ℝ)..time, ‖forcing current‖) := by
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_response_bound (Space := PeriodicC1HolderHalf)
      (diskPhysicalRateGroup frequency) (frequency • diskRotatingDerivative)
      (diskPhysicalRateGroup_zero frequency) (diskPhysicalRateGroup_add frequency)
      (diskPhysicalRateGroup_hasDerivAt frequency) diskPhysicalGroupBound_nonnegative
      (diskPhysicalRateGroup_norm_bound frequency) trajectoryContinuous forcingContinuous equation inside

end

end EulerNonuniqueness.Paper
