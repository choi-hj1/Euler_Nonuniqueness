import EulerNonuniqueness.Section8.TailCompactness
import EulerNonuniqueness.Section8.CompactnessProof

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem exists_tail_global_limit_local_ae
    {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : TailCompactnessHypotheses initial sequence) :
    ∃ subsequence : ℕ → ℕ, ∃ localLimit : ℕ → Evolution, ∃ limit : Evolution,
      StrictMono subsequence ∧
      (∀ stage : ℕ, IsEulerSolutionOn (stage + 1) initial (localLimit stage)) ∧
      (∀ stage : ℕ, ∀ time ∈ Icc (0 : ℝ) (stage + 1),
        localLimit stage time =ᵐ[volume] limit time) ∧
      (∀ stage : ℕ, ∀ exponent : ℝ, 1 ≤ exponent →
        UniformLpConvergenceOn (stage + 1) (ENNReal.ofReal exponent)
          (sequence ∘ subsequence) limit) ∧
      (∀ stage : ℕ, UniformLpConvergenceOn (stage + 1) 2
        (fun index time => biotSavart (sequence (subsequence index) time))
        (fun time => biotSavart (limit time))) ∧
      (∀ horizon : ℝ, AEStronglyMeasurable (Function.uncurry limit) (spacetimeMeasure horizon)) := by
  obtain ⟨subsequence, localLimit, increasing, properties⟩ :=
    exists_diagonal_tail_local_limits lemma81 hypotheses
  let limit : Evolution := fun time => localLimit (Nat.ceil time) time
  have equality : ∀ stage : ℕ, ∀ time ∈ Icc (0 : ℝ) (stage + 1),
      localLimit stage time =ᵐ[volume] limit time := by
    intro stage time inside
    apply diagonal_tail_local_limits_compatible (hypotheses.subsequence increasing)
      (fun stage => (properties stage).1)
      (fun stage => by simpa using (properties stage).2.1 1 le_rfl)
      stage (Nat.ceil time) inside.1 inside.2
    exact (Nat.le_ceil time).trans (by linarith)
  refine ⟨subsequence, localLimit, limit, increasing, fun stage => (properties stage).1, equality, ?_, ?_, ?_⟩
  · intro stage exponent exponentBound
    exact ((properties stage).2.1 exponent exponentBound).congr_limit (equality stage)
  · intro stage
    apply ((properties stage).2.2).congr_limit
    intro time inside
    exact Filter.EventuallyEq.of_eq (biotSavart_congr_ae (equality stage time inside))
  · exact glued_limit_aestronglyMeasurable (fun stage => (properties stage).1)

theorem tail_globalization {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : TailCompactnessHypotheses initial sequence) :
    GlobalCompactnessConclusion initial sequence := by
  obtain ⟨subsequence, localLimit, limit, increasing, localSolutions, equality,
    vorticityConvergence, velocityConvergence, measurable⟩ := exists_tail_global_limit_local_ae hypotheses
  have horizonBound (horizon : ℝ) : horizon ≤ (Nat.ceil horizon : ℝ) + 1 :=
    (Nat.le_ceil horizon).trans (by linarith)
  have globalSolution : IsEulerSolution initial limit := by
    apply isEulerSolution_of_isEulerSolutionOn
    intro horizon positive
    apply ((localSolutions (Nat.ceil horizon)).mono (horizonBound horizon)).congr_ae positive.le (measurable horizon)
    intro time inside
    exact equality (Nat.ceil horizon) time ⟨inside.1, inside.2.trans (horizonBound horizon)⟩
  refine ⟨subsequence, limit, increasing, globalSolution, ?_, ?_, ?_⟩
  · intro horizon _ exponent exponentBound
    exact (vorticityConvergence (Nat.ceil horizon) exponent exponentBound).mono (horizonBound horizon)
  · intro horizon _
    exact (velocityConvergence (Nat.ceil horizon)).mono (horizonBound horizon)
  · intro time nonnegative
    obtain ⟨cutoff, localHypotheses⟩ := (hypotheses.subsequence increasing) (time + 1) (by positivity)
    have shiftIncreasing : StrictMono (fun index : ℕ => index + cutoff) :=
      fun _ _ ordered => Nat.add_lt_add_right ordered cutoff
    apply (tendsto_add_atTop_iff_nat cutoff).mp
    apply UniformLpConvergenceOn.tendsto_l1Distance
      ((show UniformLpConvergenceOn ((Nat.ceil time : ℝ) + 1) 1 (sequence ∘ subsequence) limit from
        by simpa using vorticityConvergence (Nat.ceil time) 1 le_rfl).subsequence shiftIncreasing)
      ⟨nonnegative, horizonBound time⟩
    · intro index
      exact ((localHypotheses.2.2 index).2.1.1 time ⟨nonnegative, by linarith⟩).aestronglyMeasurable
    · exact (globalSolution.integrable time nonnegative).aestronglyMeasurable

end EulerNonuniqueness
