import EulerNonuniqueness.Section3.DiskSpectralGeneratorRange
import EulerNonuniqueness.Section3.CanonicalExteriorGeneratorRange

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance exteriorNeutralCancellationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem canonicalProjectedExteriorContourField_eventually_neutral_cancellation :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
        (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (ratio : 24 * (family.patch index).radius / distance < 1) (phase : Circle),
      diskRelabelNeutralCLM
        (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)
          (family.canonicalProjectedExteriorContourField index time distance positive small separated phase
            (diskPhysicalSpectralChart point))) = 0 := by
  have chartLimit : Tendsto diskPhysicalSpectralChart (𝓝 (0 : PeriodicC1HolderHalf))
      (𝓝 standardCircleBanach) := by
    simpa only [diskPhysicalSpectralChart_zero] using
      diskPhysicalSpectralChart_hasLipschitzDerivativeNear.lipschitzNear.continuousAt.tendsto
  have chartNear : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskPhysicalSpectralChart point - standardCircleBanach‖ <
        min (1 / 3) (min 1 (2 / (3 * Real.pi))) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using chartLimit.eventually
      (Metric.ball_mem_nhds standardCircleBanach
        (show (0 : ℝ) < min (1 / 3) (min 1 (2 / (3 * Real.pi))) by positivity))
  have angularSmall : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskNeutralCLM point‖ < 1 / 2 := by
    have limit : Tendsto diskNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
      simpa only [map_zero] using diskNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using limit.eventually
      (Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [diskPhysicalSpectralInverseDerivative_eventually_generator_range_neutral_zero,
    chartNear, angularSmall] with point annihilates nearby angularBound neutral
  intro count family index time distance positive small separated ratio phase
  have shape := diskPhysicalSpectralChart_stationary_relabel point neutral
  have relabelNear : ‖diskRelabelCurve (diskNeutralCLM point) 1 - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))) := by simpa only [shape] using nearby
  obtain ⟨preimage, actualRange⟩ := family.canonicalProjectedExteriorContourField_relabel_mem_generator_range
    index time distance positive small separated ratio (diskNeutralCLM point) angularBound
    (diskNeutralCLM_real point) relabelNear phase
  have derivative := diskEulerRotatingField_hasFDerivAt_relabel (diskNeutralCLM point)
    (relabelNear.trans_le (min_le_right _ _))
  rw [derivative.fderiv, ← shape] at actualRange
  rw [← actualRange]
  exact annihilates neutral preimage

end EulerNonuniqueness.Paper
