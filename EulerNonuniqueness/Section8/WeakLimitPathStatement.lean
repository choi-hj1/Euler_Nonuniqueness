import EulerNonuniqueness.Section8.CompactnessStatement

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

structure WeakVorticityLimitPath (horizon : ℝ) (sequence : ℕ → Evolution)
    (subsequence : ℕ → ℕ) (limit : Evolution) : Prop where
  measurable : Measurable
    (fun point : Icc (0 : ℝ) horizon × Plane => limit point.1 point.2)
  datum : ∀ time ∈ Icc 0 horizon, InitialDatum (limit time)
  weakL2Continuous : WeakL2ContinuousOn horizon limit
  supported : ∃ radius : ℝ, 0 < radius ∧ ∀ time ∈ Icc 0 horizon,
    Function.support (limit time) ⊆ Metric.closedBall 0 radius
  uniformBounds : ∀ exponent : ℝ, 1 ≤ exponent → ∃ bound : ℝ≥0∞, bound < ∞ ∧
    ∀ time ∈ Icc 0 horizon, eLpNorm (limit time) (ENNReal.ofReal exponent) volume ≤ bound
  continuousVelocity : ContinuousInLpOn horizon 2 (fun time => biotSavart (limit time))
  uniformVelocity : UniformLpConvergenceOn horizon 2
    (fun index time => biotSavart (sequence (subsequence index) time))
    (fun time => biotSavart (limit time))
  uniformMoments : ∀ test : Vorticity, MemLp test 2 volume →
    TendstoUniformly
      (fun index (time : Icc (0 : ℝ) horizon) =>
        ∫ position, sequence (subsequence index) time position * test position)
      (fun time => ∫ position, limit time position * test position) atTop

end EulerNonuniqueness
