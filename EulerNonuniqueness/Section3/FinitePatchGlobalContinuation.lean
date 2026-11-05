import EulerNonuniqueness.Section3.FinitePatchAnalytic
import EulerNonuniqueness.Section3.FinitePatchSupport
import EulerNonuniqueness.Section8.BoundedTerminalContinuation
import EulerNonuniqueness.Section8.SourceSpeedConservation

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.exists_global_continuation
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (positive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {radius : ℝ} (radiusPositive : 0 < radius)
    (supported : ∀ time ∈ Icc 0 horizon,
      support (patchVorticity scales motion time) ⊆ Metric.closedBall 0 radius) :
    ∃ omega : Evolution, IsEulerSolution (patchVorticity scales motion 0) omega ∧
      (∀ time : ℝ, time ≤ horizon → omega time = patchVorticity scales motion time) ∧
      (∀ time : ℝ, 0 ≤ time → support (omega time) ⊆ Metric.closedBall 0
        (radius + regularizedSourceSpeed (patchVorticity scales motion 0) * time)) ∧
      ∀ time : ℝ, 0 ≤ time → InitialDatum (omega time) := by
  have analytic := evolution.transportAnalyticHypotheses amplitudePositive frequencyPositive ratioPositive
    ⟨radius, radiusPositive, supported⟩
  have terminalInside : horizon ∈ Icc 0 horizon := ⟨positive.le, le_rfl⟩
  have initialInside : (0 : ℝ) ∈ Icc 0 horizon := ⟨le_rfl, positive.le⟩
  have speedEqual := (analytic.isEulerSolutionOn positive analytic.continuousInLp_biotSavart).sourceSpeed_eq_initial
    (evolution.measurable_vorticity initialInside).aestronglyMeasurable terminalInside
  obtain ⟨omega, solution, retained, growingSupport, datums⟩ := analytic.exists_global_continuation positive
    (evolution.measurable_vorticity terminalInside)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun position => norm_patchVorticity_le_sum scales motion horizon position) radiusPositive supported
  exact ⟨omega, solution, retained, by simpa only [speedEqual] using growingSupport, datums⟩

theorem FinitePatchEvolution.sourceSpeed_le_tsum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha) :
    regularizedSourceSpeed (patchVorticity scales motion time) ≤
      (4 * ∑' index : ℕ, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / (4 : ℝ))) *
          (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
            (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (4 * ∑' index : ℕ, scales.amplitude * scales.omega (index + 1) ^ 4 *
        (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / (1 : ℝ))) * (1 / (2 * Real.pi)) := by
  have properties := evolution.2.2.2.1 time inside
  apply regularizedSourceSpeed_le_of_eLpNorm_bounds (evolution.measurable_vorticity inside).aestronglyMeasurable
  · simpa only [ENNReal.ofReal_one] using patchVorticity_eLpNorm_toReal_le_tsum scales motion time
      (fun index patch => (properties index patch).1) (fun index patch => (properties index patch).2.1)
      (fun index patch => (properties index patch).2.2.1) amplitudePositive frequencyPositive ratioGreaterOne
      alphaPositive (exponent := 1) le_rfl
  · exact patchVorticity_eLpNorm_toReal_le_tsum scales motion time
      (fun index patch => (properties index patch).1) (fun index patch => (properties index patch).2.1)
      (fun index patch => (properties index patch).2.2.1) amplitudePositive frequencyPositive ratioGreaterOne
      alphaPositive (exponent := 4) (by norm_num)

end EulerNonuniqueness.Paper
