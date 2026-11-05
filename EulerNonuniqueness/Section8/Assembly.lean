import EulerNonuniqueness.Statement
import EulerNonuniqueness.General.Observation
import EulerNonuniqueness.Section8.Globalization
import EulerNonuniqueness.Section8.CompactnessProof

/-!
# Kernel-checked final separation argument

This file proves the last implication of Section 8 from actual function-valued
Euler sequences. Local compactness is `lemma81`; globalization is proved in
`Section8.Globalization`.
-/

open MeasureTheory Filter
open scoped Topology
open scoped ContDiff

namespace EulerNonuniqueness

structure ApproximationData where
  initial : Vorticity
  initialDatum : InitialDatum initial
  first : ℕ → Evolution
  second : ℕ → Evolution
  firstHypotheses : GlobalCompactnessHypotheses initial first
  secondHypotheses : GlobalCompactnessHypotheses initial second
  observation : Plane → ℝ
  observationSmooth : ContDiff ℝ ∞ observation
  observationCompact : HasCompactSupport observation
  observationBounds : ∀ position, 0 ≤ observation position ∧ observation position ≤ 1
  mass : ℝ
  massPositive : 0 < mass
  firstObservation : ∀ index, weightedAbsIntegral volume observation (first index 1) = 0
  secondObservation : ∀ index, weightedAbsIntegral volume observation (second index 1) = mass

theorem nonuniqueness_of_approximation_data
    (data : ApproximationData) : Theorem11 := by
  obtain ⟨firstSubsequence, firstLimit, firstStrict, firstSolution, firstConvergence,
      firstVelocityConvergence, firstL1Convergence⟩ :=
    globalization lemma81 data.initial data.first data.firstHypotheses
  obtain ⟨secondSubsequence, secondLimit, secondStrict, secondSolution, secondConvergence,
      secondVelocityConvergence, secondL1Convergence⟩ :=
    globalization lemma81 data.initial data.second data.secondHypotheses
  have observationMeasurable : AEStronglyMeasurable data.observation volume :=
    data.observationSmooth.continuous.aestronglyMeasurable
  have observationBounds : ∀ᵐ position ∂(volume : Measure Plane),
      0 ≤ data.observation position ∧ data.observation position ≤ 1 :=
    Filter.Eventually.of_forall data.observationBounds
  have firstObserved : weightedAbsIntegral volume data.observation (firstLimit 1) = 0 := by
    apply weightedAbsIntegral_eq_of_tendsto_integral_abs_sub observationMeasurable observationBounds
      (fun index => data.firstHypotheses.integrable (firstSubsequence index) 1 zero_le_one)
      (firstSolution.integrable 1 zero_le_one) (firstL1Convergence 1 zero_le_one)
    exact Filter.Eventually.of_forall (fun index => data.firstObservation (firstSubsequence index))
  have secondObserved : weightedAbsIntegral volume data.observation (secondLimit 1) = data.mass := by
    apply weightedAbsIntegral_eq_of_tendsto_integral_abs_sub observationMeasurable observationBounds
      (fun index => data.secondHypotheses.integrable (secondSubsequence index) 1 zero_le_one)
      (secondSolution.integrable 1 zero_le_one) (secondL1Convergence 1 zero_le_one)
    exact Filter.Eventually.of_forall (fun index => data.secondObservation (secondSubsequence index))
  refine ⟨data.initial, firstLimit, secondLimit, data.initialDatum,
    firstSolution, secondSolution, ?_⟩
  exact integral_abs_sub_pos_of_weightedAbsIntegral observationMeasurable observationBounds
    (firstSolution.integrable 1 zero_le_one) (secondSolution.integrable 1 zero_le_one)
    firstObserved secondObserved data.massPositive

end EulerNonuniqueness
