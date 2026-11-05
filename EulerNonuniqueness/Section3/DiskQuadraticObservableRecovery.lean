import EulerNonuniqueness.Section3.DiskNormalizedQuadraticObservable
import EulerNonuniqueness.General.QuadraticCoordinateSeparation
import EulerNonuniqueness.General.LocalLipschitzCenteredBounds

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance quadraticObservableRecoveryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskSpectralQuadraticObservable_exists_uniform_transverse_recovery :
    ∃ radius > 0, ∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ radius →
      ‖diskPhysicalTransverseProjection data‖ ≤ 2 * ‖diskSpectralQuadraticObservable data‖ := by
  have neutralContinuous : ContinuousAt
      (diskRelabelNeutralCLM : PeriodicC1HolderHalf → PeriodicC1HolderHalf) 0 := diskRelabelNeutralCLM.continuous.continuousAt
  have correctionContinuous : ContinuousAt
      (fun data : PeriodicC1HolderHalf => diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM data)) 0 := by
    have outer : ContinuousAt diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by
      simpa only [map_zero] using diskSpectralMovingQuadraticCorrection_lipschitzNear.continuousAt
    exact outer.comp neutralContinuous
  have transverseContinuous : ContinuousAt
      (diskPhysicalTransverseProjection : PeriodicC1HolderHalf → PeriodicC1HolderHalf) 0 :=
    diskPhysicalTransverseProjection.continuous.continuousAt
  have productContinuous : ContinuousAt
      (fun data : PeriodicC1HolderHalf =>
        (2 * ‖diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM data)‖) *
          ‖diskPhysicalTransverseProjection data‖) 0 :=
    (correctionContinuous.norm.const_mul 2).mul transverseContinuous.norm
  have small : ∀ᶠ data in 𝓝 (0 : PeriodicC1HolderHalf),
      (2 * ‖diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM data)‖) *
        ‖diskPhysicalTransverseProjection data‖ ≤ 1 / 2 := by
    apply (productContinuous.tendsto.eventually (eventually_lt_nhds (by simp :
      (2 * ‖diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf))‖) *
        ‖diskPhysicalTransverseProjection 0‖ < (1 / 2 : ℝ)))).mono
    intro data strict
    exact strict.le
  obtain ⟨outerRadius, positive, contained⟩ := Metric.eventually_nhds_iff.mp small
  refine ⟨outerRadius / 2, by positivity, ?_⟩
  intro data nearby
  have actualSmall := contained (show dist data (0 : PeriodicC1HolderHalf) < outerRadius by
    rw [dist_zero_right]
    exact nearby.trans_lt (by linarith))
  have separation := EulerNonuniqueness.General.quadraticCoordinate_separation
    (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM data)) 1
    (diskPhysicalTransverseProjection data) 0 (le_refl _) (by simp)
    (by simpa only [abs_one, div_one] using actualSmall)
  simp only [diskSpectralQuadraticObservable, sub_zero, EulerNonuniqueness.General.quadraticCoordinate,
    map_zero, div_one, one_smul, sub_zero] at separation ⊢
  linarith

theorem diskNormalizedQuadraticObservable_exists_uniform_difference_bound :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ first second : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖second - standardCircleBanach‖ ≤ radius →
      ‖diskNormalizedQuadraticObservable first - diskNormalizedQuadraticObservable second‖ ≤ constant * ‖first - second‖ :=
  diskNormalizedQuadraticObservable_lipschitzNear_circle.exists_centered_closedBall_difference_bound

end EulerNonuniqueness.Paper
