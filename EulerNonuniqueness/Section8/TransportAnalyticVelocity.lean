import EulerNonuniqueness.Section8.TransportAnalyticHypotheses
import EulerNonuniqueness.Section8.WeakVelocityContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.continuous_biotSavart
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) : Continuous (biotSavart (omega time)) := by
  obtain ⟨radius, positive, supported⟩ := hypotheses.supported
  exact continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (hypotheses.membership 4 (by norm_num) time inside) (by norm_num) positive.le (supported time inside)

theorem TransportAnalyticHypotheses.biotSavart_memLp_two
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) : MemLp (biotSavart (omega time)) 2 volume := by
  obtain ⟨radius, positive, supported⟩ := hypotheses.supported
  exact memLp_biotSavart_two_of_memLp_support_integral_zero holderConjugate_four_fourThirds
    (hypotheses.membership 4 (by norm_num) time inside) (by norm_num)
    (hypotheses.integrable inside) (hypotheses.zeroMean time inside) positive.le (supported time inside)

theorem TransportAnalyticHypotheses.uniform_biotSavart_bound_on_closedBall
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) {observationRadius : ℝ}
    (observationNonnegative : 0 ≤ observationRadius) :
    ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧ ∀ time ∈ Icc 0 horizon,
      ∀ position ∈ Metric.closedBall (0 : Plane) observationRadius,
        ENNReal.ofReal ‖biotSavart (omega time) position‖ ≤ bound := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  obtain ⟨bound, boundFinite, bounded⟩ := hypotheses.uniformBounds 4 (by norm_num)
  have kernelMember := (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (memLp_biotSavartKernel_ball (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)
      (show 0 < observationRadius + radius + 1 by positivity))
  refine ⟨bound * eLpNorm ((Metric.ball 0 (observationRadius + radius + 1)).indicator
    biotSavartKernel) (ENNReal.ofReal (4 / 3)) volume,
    ENNReal.mul_lt_top boundFinite kernelMember.eLpNorm_lt_top, ?_⟩
  intro time inside position positionBound
  exact (enorm_biotSavart_le_eLpNorm_of_memLp_support holderConjugate_four_fourThirds
    (hypotheses.membership 4 (by norm_num) time inside) (by norm_num)
    radiusPositive.le observationNonnegative (supported time inside)
    (show ‖position‖ ≤ observationRadius by simpa using positionBound)).trans
      (mul_le_mul_right' (bounded time inside) _)

theorem TransportAnalyticHypotheses.continuous_biotSavart_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon => biotSavart (omega time) position) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  obtain ⟨bound, finite, bounded⟩ := hypotheses.uniformBounds 4 (by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro time
  apply tendsto_biotSavart_of_weakL2_uniform_memLp_support
    holderConjugate_four_fourThirds (by norm_num) radiusPositive.le
    (fun other : Icc (0 : ℝ) horizon => hypotheses.membership 4 (by norm_num) other other.property)
    (hypotheses.membership 4 (by norm_num) time time.property)
    (fun other : Icc (0 : ℝ) horizon => supported other other.property)
    (supported time time.property) (bound := bound.toReal)
  · intro other
    exact ENNReal.toReal_mono finite.ne (bounded other other.property)
  · intro test member
    exact (hypotheses.weakL2Continuous.2 test member).tendsto time

end EulerNonuniqueness
