import EulerNonuniqueness.Section8.WeakVorticityPath

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.velocity_lift_eLpNorm_le
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (subsequence : ℕ → ℕ)
    {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity}
    (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {exponent : ℝ≥0∞} (exponentBound : 1 ≤ exponent) {bound : ℝ≥0∞}
    (bounded : ∀ index, ∀ time ∈ Icc 0 horizon, eLpNorm (sequence index time) exponent volume ≤ bound)
    (time : Icc (0 : ℝ) horizon) : eLpNorm (fields time) exponent volume ≤ bound := by
  apply eLpNorm_le_of_weakL2_tendsto_functions
    (filter := atTop) (sequence := fun index => sequence (subsequence index) time)
    (fun index => ((hypotheses.2.2 (subsequence index)).2.1.1 time time.property))
    (by simpa using (datums time).2.1 2 (by norm_num)) exponentBound
    (fun index => bounded (subsequence index) time time.property)
  intro test testMember
  exact (hypotheses.uniform_moment_of_uniform_velocity_limit horizonNonnegative subsequence
    uniform datums equal testMember).tendsto_at time

theorem LocalCompactnessHypotheses.velocity_lift_ae_indicator
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (subsequence : ℕ → ℕ)
    {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity}
    (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {radius : ℝ}
    (supported : ∀ index, ∀ time ∈ Icc 0 horizon,
      Function.support (sequence index time) ⊆ Metric.closedBall 0 radius)
    (time : Icc (0 : ℝ) horizon) :
    fields time =ᵐ[volume] (Metric.closedBall 0 radius).indicator (fields time) := by
  apply ae_eq_indicator_of_weakL2_tendsto_of_support
    (filter := atTop) (sequence := fun index => sequence (subsequence index) time) measurableSet_closedBall
    (by simpa using (datums time).2.1 2 (by norm_num))
    (fun index => supported (subsequence index) time time.property)
  intro test testMember
  exact (hypotheses.uniform_moment_of_uniform_velocity_limit horizonNonnegative subsequence
    uniform datums equal testMember).tendsto_at time

end EulerNonuniqueness
