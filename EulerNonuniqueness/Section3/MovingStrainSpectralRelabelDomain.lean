import EulerNonuniqueness.Section3.DiskPhysicalSpectralDefectBounds
import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseLipschitz
import EulerNonuniqueness.Section3.DiskNeutralContinuousVectors
import EulerNonuniqueness.Section3.FixedRelabelEquivalence

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance affineRelabelDomainC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem movingStrainSpectral_exists_relabel_domain {budget : ℝ} (positive : 0 < budget) :
    ∃ radius > 0, ∀ state : PeriodicC1HolderHalf, state ∈ ball 0 radius →
      ‖diskNeutralCLM state‖ < 1 / 2 ∧
      ‖diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach‖ <
        min (1 / 3) (min 1 (2 / (3 * Real.pi))) ∧
      ‖diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach‖ < budget ∧
      ‖diskPhysicalSpectralDefect state‖ < budget := by
  have neutralContinuous : ContinuousAt (fun state => diskRelabelNeutralCLM state)
      (0 : PeriodicC1HolderHalf) := diskRelabelNeutralCLM.continuous.continuousAt
  have chartContinuous : ContinuousAt diskStationaryChart
      (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by
    rw [map_zero]
    exact (diskStationaryChart_analyticAt 0).continuousAt
  have baseContinuous : ContinuousAt
      (fun state => diskStationaryChart (diskRelabelNeutralCLM state)) (0 : PeriodicC1HolderHalf) :=
    chartContinuous.comp neutralContinuous
  have baseZero : diskStationaryChart (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) =
      standardCircleBanach := by rw [map_zero, diskStationaryChart_zero]
  have defectContinuous : ContinuousAt diskPhysicalSpectralDefect (0 : PeriodicC1HolderHalf) := by
    exact diskPhysicalSpectralChart_hasLipschitzDerivativeNear.lipschitzNear.continuousAt.sub baseContinuous
  have defectZero : diskPhysicalSpectralDefect (0 : PeriodicC1HolderHalf) = 0 := by
    rw [diskPhysicalSpectralDefect, diskPhysicalSpectralChart_zero, baseZero, sub_self]
  have angularNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskNeutralCLM state‖ < 1 / 2 := by
    have convergence : Tendsto (fun state => ‖diskNeutralCLM state‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      have actual : ContinuousAt (fun state => diskNeutralCLM state) (0 : PeriodicC1HolderHalf) :=
        diskNeutralCLM.continuous.continuousAt
      simpa only [map_zero, norm_zero] using actual.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have baseNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach‖ <
        min (min (1 / 3) (min 1 (2 / (3 * Real.pi)))) budget := by
    have convergence : Tendsto
        (fun state => ‖diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      have actual : ContinuousAt
          (fun state => diskStationaryChart (diskRelabelNeutralCLM state) - standardCircleBanach)
          (0 : PeriodicC1HolderHalf) := baseContinuous.sub continuousAt_const
      simpa only [baseZero, sub_self, norm_zero] using actual.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds (by positivity))
  have defectNear : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskPhysicalSpectralDefect state‖ < budget := by
    have convergence : Tendsto (fun state => ‖diskPhysicalSpectralDefect state‖)
        (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
      simpa only [defectZero, norm_zero] using defectContinuous.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds positive)
  obtain ⟨radius, radiusPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    (angularNear.and (baseNear.and defectNear))
  refine ⟨radius, radiusPositive, ?_⟩
  intro state inside
  have valid := contained (by simpa only [mem_ball] using inside)
  exact ⟨valid.1, valid.2.1.trans_le (min_le_left _ _),
    valid.2.1.trans_le (min_le_right _ _), valid.2.2⟩

theorem movingStrainSpectral_stationary_base_eq_fixedRelabel (state : PeriodicC1HolderHalf)
    (small : ‖diskNeutralCLM state‖ < 1 / 2) :
    diskStationaryChart (diskRelabelNeutralCLM state) =
      fixedRelabelEquivalence (diskNeutralCLM state) small standardCircleBanach := by
  rw [fixedRelabelEquivalence_circle _ small (diskNeutralCLM_real state), diskRelabelNeutralCLM_apply,
    diskStationaryChart_relabel _ (diskNeutralCLM_real state)]

end EulerNonuniqueness.Paper
