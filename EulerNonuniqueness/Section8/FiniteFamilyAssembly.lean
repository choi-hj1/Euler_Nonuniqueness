import EulerNonuniqueness.Section8.PatchFamilyCompactness
import EulerNonuniqueness.Section8.Assembly

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem exists_approximationData_of_finite_patch_families
    {firstCounts secondCounts : ℕ → ℕ} {scales : Scales}
    {firstMotions : (index : ℕ) → PatchMotion (firstCounts index)}
    {secondMotions : (index : ℕ) → PatchMotion (secondCounts index)}
    (firstEvolutions : ∀ index, FinitePatchEvolution scales (firstMotions index) 1)
    (secondEvolutions : ∀ index, FinitePatchEvolution scales (secondMotions index) 1)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (firstSupported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (firstMotions index) time) ⊆ Metric.closedBall 0 radius)
    (secondSupported : ∀ index, ∀ time ∈ Icc 0 1,
      support (patchVorticity scales (secondMotions index) time) ⊆ Metric.closedBall 0 radius)
    {initial : Vorticity} (datum : InitialDatum initial)
    (firstInitialConvergence : InitialLpConvergence (fun index => patchVorticity scales (firstMotions index)) initial)
    (secondInitialConvergence : InitialLpConvergence (fun index => patchVorticity scales (secondMotions index)) initial)
    {observation : Plane → ℝ} (smooth : ContDiff ℝ ∞ observation) (compact : HasCompactSupport observation)
    (bounded : ∀ position, 0 ≤ observation position ∧ observation position ≤ 1)
    {mass : ℝ} (massPositive : 0 < mass)
    (firstObserved : ∀ index, weightedAbsIntegral volume observation (patchVorticity scales (firstMotions index) 1) = 0)
    (secondObserved : ∀ index, weightedAbsIntegral volume observation (patchVorticity scales (secondMotions index) 1) = mass) :
    Nonempty ApproximationData := by
  obtain ⟨first, firstHypotheses, firstRetained⟩ := exists_global_compact_patch_family firstEvolutions
    amplitudePositive frequencyPositive ratioGreaterOne alphaPositive radiusPositive firstSupported firstInitialConvergence
  obtain ⟨second, secondHypotheses, secondRetained⟩ := exists_global_compact_patch_family secondEvolutions
    amplitudePositive frequencyPositive ratioGreaterOne alphaPositive radiusPositive secondSupported secondInitialConvergence
  refine ⟨⟨initial, datum, first, second, firstHypotheses, secondHypotheses, observation,
    smooth, compact, bounded, mass, massPositive, ?_, ?_⟩⟩
  · intro index
    rw [firstRetained index 1 le_rfl]
    exact firstObserved index
  · intro index
    rw [secondRetained index 1 le_rfl]
    exact secondObserved index

end EulerNonuniqueness.Paper
