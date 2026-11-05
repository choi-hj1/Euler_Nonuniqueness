import EulerNonuniqueness.Section4.InitialDiskUniformBounds
import EulerNonuniqueness.Section1.DiskInitialCompactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

def referenceInitialCenters {count : ℕ} (scales : Scales) (phase unstable : Fin count → ℝ) :
    ℕ → Fin 4 → Plane := fun index patch =>
  if inside : index < count then initialDiskCenter scales (index + 1) (phase ⟨index, inside⟩)
    (unstable ⟨index, inside⟩) patch else 0

theorem reference_initial_quadrupole_eq_disk {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (phase unstable : Fin count → ℝ) (threshold : ℝ)
    (initialDisks : ReferenceInitialDisks scales motion phase unstable threshold) (index : Fin count) :
    quadrupoleDensity scales motion 0 index =
      diskQuadrupoleDensity scales (referenceInitialCenters scales phase unstable) index.val := by
  funext position
  simp only [quadrupoleDensity, diskQuadrupoleDensity, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro patch _
  unfold patchDensity diskDensity
  rw [(initialDisks index).2 patch |>.1]
  simp only [referenceInitialCenters, dif_pos index.isLt]

theorem reference_initial_vorticity_eq_disk_sum {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (phase unstable : Fin count → ℝ) (threshold : ℝ)
    (initialDisks : ReferenceInitialDisks scales motion phase unstable threshold) :
    patchVorticity scales motion 0 = ∑ index ∈ Finset.range count,
      diskQuadrupoleDensity scales (referenceInitialCenters scales phase unstable) index := by
  funext position
  simp only [patchVorticity, Finset.sum_apply]
  simp_rw [reference_initial_quadrupole_eq_disk scales motion phase unstable threshold initialDisks]
  exact Fin.sum_univ_eq_sum_range
    (fun index => diskQuadrupoleDensity scales (referenceInitialCenters scales phase unstable) index position) count

theorem referenceInitialCenters_norm_bound {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (phase unstable : Fin count → ℝ) {threshold : ℝ}
    (initialDisks : ReferenceInitialDisks scales motion phase unstable threshold)
    (thresholdBound : threshold ≤ 1) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) (patch : Fin 4) :
    ‖referenceInitialCenters scales phase unstable index patch‖ ≤ 3 := by
  dsimp only [referenceInitialCenters]
  split_ifs with inside
  · exact initialDiskCenter_norm_le_three scales (index + 1) _ _ frequencyPositive ratioPositive
      ((initialDisks ⟨index, inside⟩).1.trans thresholdBound) patch
  · simp

theorem exists_common_initialDatum_of_reference_disks (scales : Scales)
    {counts : ℕ → ℕ} (countsTendsto : Tendsto counts atTop atTop)
    (motions : (step : ℕ) → PatchMotion (counts step))
    (phase unstable : (step : ℕ) → Fin (counts step) → ℝ) {threshold : ℝ}
    (initialDisks : ∀ step, ReferenceInitialDisks scales (motions step) (phase step) (unstable step) threshold)
    (thresholdBound : threshold ≤ 1) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    ∃ initial : Vorticity, InitialDatum initial ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        ∀ exponent : ℝ, 1 ≤ exponent → Tendsto
          (fun step => eLpNorm (patchVorticity scales (motions (subsequence step)) 0 - initial)
            (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  let centers := fun step => referenceInitialCenters scales (phase step) (unstable step)
  have centerBound (step index : ℕ) (patch : Fin 4) : ‖centers step index patch‖ ≤ 3 :=
    referenceInitialCenters_norm_bound scales (motions step) (phase step) (unstable step)
      (initialDisks step) thresholdBound frequencyPositive (zero_lt_one.trans ratioGreaterOne) index patch
  let radius := 3 + Real.sqrt (2 / (scales.amplitude * scales.frequency ^ 3))
  have supported (step index : ℕ) (patch : Fin 4) :
      Metric.ball (centers step index patch) (scales.radius (index + 1)) ⊆ Metric.closedBall (0 : Plane) radius := by
    intro position inside
    rw [Metric.mem_closedBall, dist_zero_right]
    have triangle : ‖position‖ ≤ ‖position - centers step index patch‖ + ‖centers step index patch‖ := by
      simpa only [sub_add_cancel] using norm_add_le (position - centers step index patch) (centers step index patch)
    have nearby : ‖position - centers step index patch‖ < scales.radius (index + 1) :=
      by simpa only [Metric.mem_ball, dist_eq_norm] using inside
    have radiusBound := scales.radius_uniform_bound amplitudePositive frequencyPositive ratioGreaterOne.le (index + 1)
    dsimp only [radius]
    linarith [centerBound step index patch]
  obtain ⟨initial, initialDatum, _, subsequence, increasing, converges⟩ :=
    exists_common_initialDatum_of_disk_arrays scales centers amplitudePositive frequencyPositive ratioGreaterOne alphaPositive
      countsTendsto (isCompact_closedBall (0 : Plane) 3)
      (fun step index patch => by simpa only [Metric.mem_closedBall, dist_zero_right] using centerBound step index patch)
      (isCompact_closedBall (0 : Plane) radius) supported
  refine ⟨initial, initialDatum, subsequence, increasing, fun exponent exponentBound => ?_⟩
  have identities (step : ℕ) := reference_initial_vorticity_eq_disk_sum scales (motions (subsequence step))
    (phase (subsequence step)) (unstable (subsequence step)) threshold (initialDisks (subsequence step))
  simpa only [identities, centers] using converges exponent exponentBound

end EulerNonuniqueness.Paper
