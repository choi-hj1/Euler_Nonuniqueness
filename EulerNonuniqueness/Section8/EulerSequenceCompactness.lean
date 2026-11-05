import EulerNonuniqueness.Section8.EulerSolutionRestriction

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem globalCompactnessHypotheses_of_euler_solutions
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (initialConvergence : InitialLpConvergence sequence initial)
    (solutions : ∀ index, IsEulerSolution (sequence index 0) (sequence index))
    (supported : ∀ horizon : ℝ, 0 < horizon → ∃ radius : ℝ, 0 < radius ∧
      ∀ index, ∀ time ∈ Icc 0 horizon, Function.support (sequence index time) ⊆ Metric.closedBall 0 radius)
    (zeroMean : ∀ index, ∀ time : ℝ, 0 ≤ time → (∫ position, sequence index time position) = 0) :
    GlobalCompactnessHypotheses initial sequence := by
  intro horizon positive
  refine ⟨initialConvergence, supported horizon positive, ?_⟩
  intro index
  have solution := (solutions index).on_interval positive
  refine ⟨solution.2.2.2.2.2.2.1, solution.weakL2ContinuousOn,
    fun time inside => ⟨solution.2.2.2.1 time inside, zeroMean index time inside.1⟩, ?_⟩
  intro exponent exponentBound time inside
  exact ⟨solution.memLp exponentBound inside, solution.2.2.2.2.1 exponent exponentBound time inside⟩

end EulerNonuniqueness
