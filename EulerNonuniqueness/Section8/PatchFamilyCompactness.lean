import EulerNonuniqueness.Section3.FinitePatchGlobalContinuation
import EulerNonuniqueness.Section8.EulerSequenceCompactness

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_global_patch_family
    {counts : ℕ → ℕ} {scales : Scales} {motions : (index : ℕ) → PatchMotion (counts index)}
    (evolutions : ∀ index, FinitePatchEvolution scales (motions index) 1)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (supported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (motions index) time) ⊆ Metric.closedBall 0 radius) :
    ∃ sequence : ℕ → Evolution,
      (∀ index, IsEulerSolution (patchVorticity scales (motions index) 0) (sequence index)) ∧
      (∀ index, ∀ time : ℝ, time ≤ 1 → sequence index time = patchVorticity scales (motions index) time) ∧
      (∀ horizon : ℝ, 0 < horizon → ∃ bound : ℝ, 0 < bound ∧
        ∀ index, ∀ time ∈ Icc 0 horizon, support (sequence index time) ⊆ Metric.closedBall 0 bound) ∧
      ∀ index, ∀ time : ℝ, 0 ≤ time → InitialDatum (sequence index time) := by
  have existence (index : ℕ) := (evolutions index).exists_global_continuation zero_lt_one
    amplitudePositive frequencyPositive (zero_lt_one.trans ratioGreaterOne) radiusPositive (supported index)
  choose sequence solutions retained growingSupport datums using existence
  let speedBound :=
      (4 * ∑' index : ℕ, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / (4 : ℝ))) *
          (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
            (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (4 * ∑' index : ℕ, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / (1 : ℝ))) * (1 / (2 * Real.pi))
  have speedBounded (index : ℕ) : regularizedSourceSpeed (patchVorticity scales (motions index) 0) ≤ max speedBound 0 :=
    ((evolutions index).sourceSpeed_le_tsum (time := 0) ⟨le_rfl, zero_le_one⟩
      amplitudePositive frequencyPositive ratioGreaterOne alphaPositive).trans (le_max_left speedBound 0)
  refine ⟨sequence, solutions, retained, ?_, datums⟩
  intro horizon positive
  refine ⟨radius + max speedBound 0 * horizon, by positivity, ?_⟩
  intro index time inside
  apply (growingSupport index time inside.1).trans
  apply Metric.closedBall_subset_closedBall
  exact add_le_add_left (mul_le_mul (speedBounded index) inside.2 inside.1 (le_max_right speedBound 0)) radius

theorem exists_global_compact_patch_family
    {counts : ℕ → ℕ} {scales : Scales} {motions : (index : ℕ) → PatchMotion (counts index)}
    (evolutions : ∀ index, FinitePatchEvolution scales (motions index) 1)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (supported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (motions index) time) ⊆ Metric.closedBall 0 radius)
    {initial : Vorticity}
    (initialConvergence : InitialLpConvergence (fun index => patchVorticity scales (motions index)) initial) :
    ∃ sequence : ℕ → Evolution, GlobalCompactnessHypotheses initial sequence ∧
      ∀ index, ∀ time : ℝ, time ≤ 1 → sequence index time = patchVorticity scales (motions index) time := by
  obtain ⟨sequence, solutions, retained, supportedGlobal, datums⟩ := exists_global_patch_family
    evolutions amplitudePositive frequencyPositive ratioGreaterOne alphaPositive radiusPositive supported
  refine ⟨sequence, globalCompactnessHypotheses_of_euler_solutions ?_ ?_ supportedGlobal
    (fun index time nonnegative => (datums index time nonnegative).2.2), retained⟩
  · refine ⟨initialConvergence.1, ?_⟩
    intro exponent exponentBound
    simpa only [retained _ 0 zero_le_one] using initialConvergence.2 exponent exponentBound
  · intro index
    rw [retained index 0 zero_le_one]
    exact solutions index

end EulerNonuniqueness.Paper
