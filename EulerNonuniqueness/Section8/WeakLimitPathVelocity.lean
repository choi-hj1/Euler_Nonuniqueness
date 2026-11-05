import EulerNonuniqueness.Section8.WeakLimitPathStatement
import EulerNonuniqueness.Section8.SpacetimeMeasurability
import EulerNonuniqueness.Section8.InitialVelocity
import EulerNonuniqueness.Section8.WeakVelocityContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.membership
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (exponent : ℝ) (exponentBound : 1 ≤ exponent) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    MemLp (limit time) (ENNReal.ofReal exponent) volume :=
  (path.datum time inside).2.1 exponent exponentBound

theorem WeakVorticityLimitPath.continuous_biotSavart_time
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit) (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon => biotSavart (limit time) position) := by
  obtain ⟨radius, radiusPositive, supported⟩ := path.supported
  obtain ⟨bound, finite, bounded⟩ := path.uniformBounds 4 (by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro time
  apply tendsto_biotSavart_of_weakL2_uniform_memLp_support
    holderConjugate_four_fourThirds (by norm_num) radiusPositive.le
    (fun other : Icc (0 : ℝ) horizon => path.membership 4 (by norm_num) other.property)
    (path.membership 4 (by norm_num) time.property)
    (fun other : Icc (0 : ℝ) horizon => supported other other.property)
    (supported time time.property) (bound := bound.toReal)
  · intro other
    exact ENNReal.toReal_mono finite.ne (bounded other other.property)
  · intro test member
    exact (path.weakL2Continuous.2 test member).tendsto time

theorem WeakVorticityLimitPath.measurable_biotSavart
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane => biotSavart (limit point.1) point.2) :=
  (measurable_uncurry_of_continuous_of_measurable
    (fun time : Icc (0 : ℝ) horizon => (path.datum time time.property).continuous_biotSavart)
    (fun position => (path.continuous_biotSavart_time position).measurable)).comp measurable_swap

theorem WeakVorticityLimitPath.uniform_biotSavart_bound_on_closedBall
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit) {observationRadius : ℝ}
    (observationNonnegative : 0 ≤ observationRadius) :
    ∃ bound : ℝ≥0∞, bound < ∞ ∧ ∀ time ∈ Icc 0 horizon,
      ∀ position ∈ Metric.closedBall (0 : Plane) observationRadius,
        ENNReal.ofReal ‖biotSavart (limit time) position‖ ≤ bound := by
  obtain ⟨radius, radiusPositive, supported⟩ := path.supported
  obtain ⟨bound, finite, bounded⟩ := path.uniformBounds 4 (by norm_num)
  have kernelMember := (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (memLp_biotSavartKernel_ball (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)
      (show 0 < observationRadius + radius + 1 by positivity))
  refine ⟨bound * eLpNorm ((Metric.ball 0 (observationRadius + radius + 1)).indicator
    biotSavartKernel) (ENNReal.ofReal (4 / 3)) volume,
    ENNReal.mul_lt_top finite kernelMember.eLpNorm_lt_top, ?_⟩
  intro time inside position positionBound
  exact (enorm_biotSavart_le_eLpNorm_of_memLp_support holderConjugate_four_fourThirds
    (path.membership 4 (by norm_num) inside) (by norm_num)
    radiusPositive.le observationNonnegative (supported time inside)
    (show ‖position‖ ≤ observationRadius by simpa using positionBound)).trans
      (mul_le_mul_right' (bounded time inside) _)

end EulerNonuniqueness
