import EulerNonuniqueness.Section8.RegularizedPointwiseSupport
import EulerNonuniqueness.Section8.RegularizedApproximation
import EulerNonuniqueness.Section8.WeakLimitPathStatement
import EulerNonuniqueness.General.L2TestSeparation
import EulerNonuniqueness.Section8.SpacetimeMeasurability

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace EulerNonuniqueness

def growingSupportMask (radius speed : ℝ) (omega : Evolution) : Evolution :=
  fun time => (Metric.closedBall (0 : Plane) (radius + speed * time)).indicator (omega time)

theorem measurable_growingSupportMask_on_time_subtype {horizon radius speed : ℝ} {omega : Evolution}
    (measurable : Measurable (fun point : Icc 0 horizon × Plane => omega point.1 point.2)) :
    Measurable (fun point : Icc 0 horizon × Plane => growingSupportMask radius speed omega point.1 point.2) := by
  have regionMeasurable : MeasurableSet
      {point : Icc 0 horizon × Plane | ‖point.2‖ ≤ radius + speed * (point.1 : ℝ)} :=
    (isClosed_le continuous_snd.norm
      (continuous_const.add (continuous_const.mul (continuous_subtype_val.comp continuous_fst)))).measurableSet
  convert measurable.indicator regionMeasurable using 1
  ext point
  simp only [growingSupportMask, indicator_apply, mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  by_cases inside : point.2 ∈ Metric.closedBall (0 : Plane) (radius + speed * (point.1 : ℝ))
  · rw [indicator_of_mem inside]
    exact (if_pos (by simpa only [Metric.mem_closedBall, dist_zero_right] using inside)).symm
  · rw [indicator_of_not_mem inside]
    exact (if_neg (by simpa only [Metric.mem_closedBall, dist_zero_right] using inside)).symm

theorem support_growingSupportMask_subset (radius speed : ℝ) (omega : Evolution) (time : ℝ) :
    support (growingSupportMask radius speed omega time) ⊆ Metric.closedBall 0 (radius + speed * time) := by
  intro position nonzero
  by_contra outside
  exact nonzero (indicator_of_not_mem outside _)

theorem regularized_limit_ae_growingSupportMask {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {radius : ℝ} (supported : support source ⊆ Metric.closedBall 0 radius)
    {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon (regularizedApproximation integrable nonnegative) subsequence limit)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    limit time =ᵐ[volume] growingSupportMask radius (regularizedSourceSpeed source) limit time := by
  apply ae_eq_indicator_of_weakL2_tendsto_of_support
    (filter := atTop) (sequence := fun index => regularizedApproximation integrable nonnegative (subsequence index) time)
    measurableSet_closedBall (path.weakL2Continuous.1 time inside)
    (fun index => (regularizedApproximationFlow integrable nonnegative (subsequence index)).support_vorticity_subset_at_time
      nonnegative membership supported inside)
  intro test testMember
  exact (path.uniformMoments test testMember).tendsto_at ⟨time, inside⟩

theorem regularized_limit_mask_isEulerSolutionOn {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {radius : ℝ} (supported : support source ⊆ Metric.closedBall 0 radius)
    {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon (regularizedApproximation integrable nonnegative) subsequence limit)
    (solution : IsEulerSolutionOn horizon source limit) :
    IsEulerSolutionOn horizon source (growingSupportMask radius (regularizedSourceSpeed source) limit) := by
  apply solution.congr_ae nonnegative
    (aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
      (field := Function.uncurry (growingSupportMask radius (regularizedSourceSpeed source) limit))
      (measurable_growingSupportMask_on_time_subtype
        (radius := radius) (speed := regularizedSourceSpeed source) path.measurable))
  exact fun time inside => regularized_limit_ae_growingSupportMask integrable nonnegative membership supported path inside

end EulerNonuniqueness
