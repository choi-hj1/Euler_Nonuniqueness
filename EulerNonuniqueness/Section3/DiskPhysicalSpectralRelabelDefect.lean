import EulerNonuniqueness.Section3.DiskPhysicalSpectralFirstOrderBounds
import EulerNonuniqueness.Section3.DiskPhysicalSpectralGenerator
import EulerNonuniqueness.Section3.DiskSpectralProjectedBounds
import EulerNonuniqueness.Section3.DiskAngularNeutralProjection

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralRelabelDefectC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralChart_exists_uniform_relabel_defect :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ point : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM point‖ + ‖point - diskRelabelNeutralCLM point‖ ≤ radius →
      diskSpectralTubularArea point = Real.pi →
      ‖diskPhysicalSpectralChart point - diskRelabelCurve (diskNeutralCLM point) 1‖ ≤
        constant * ‖diskPhysicalTransverseProjection point‖ := by
  obtain ⟨chartRadius, chartPositive, constant, one, _, chartDifference⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨areaRadius, areaPositive, _, _, absorption⟩ :=
    diskSpectralTubularArea_exists_transverse_absorption
  refine ⟨min chartRadius areaRadius, lt_min chartPositive areaPositive,
    2 * constant, by linarith, ?_⟩
  intro point small area
  have pointIdentity : diskRelabelNeutralCLM point + (point - diskRelabelNeutralCLM point) = point := by abel
  have pointBound : ‖point‖ ≤ chartRadius := by
    have triangle := norm_add_le (diskRelabelNeutralCLM point) (point - diskRelabelNeutralCLM point)
    rw [pointIdentity] at triangle
    exact triangle.trans (small.trans (min_le_left _ _))
  have neutralBound : ‖diskRelabelNeutralCLM point‖ ≤ chartRadius := by
    have actual := small.trans (min_le_left _ _)
    linarith [norm_nonneg (point - diskRelabelNeutralCLM point)]
  have absorbed := (absorption point (small.trans (min_le_right _ _)) area).1
  rw [diskSpectralRelative_transverse] at absorbed
  have difference := (chartDifference point (diskRelabelNeutralCLM point) pointBound neutralBound).1
  have stationary := diskPhysicalSpectralChart_stationary_relabel (diskRelabelNeutralCLM point)
    (diskRelabelNeutralCLM_idempotent point)
  rw [diskNeutralCLM_relabelNeutral] at stationary
  rw [stationary] at difference
  exact difference.trans ((mul_le_mul_of_nonneg_left absorbed (by linarith : 0 ≤ constant)).trans_eq (by ring))

theorem diskPhysicalSpectralCoordinate_exists_uniform_relabel_defect :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ data : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ < radius → contourAreaFunctional data = Real.pi →
      ‖data - diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1‖ ≤
        constant * ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ := by
  obtain ⟨tubeRadius, tubePositive, constant, one, estimate⟩ :=
    diskPhysicalSpectralChart_exists_uniform_relabel_defect
  obtain ⟨radius, positive, coordinates⟩ := diskPhysicalSpectralCoordinate_exists_radius tubePositive
  refine ⟨radius, positive, constant, one, ?_⟩
  intro data small area
  obtain ⟨rightInverse, areaIdentity, tube, _⟩ := coordinates data small
  have actualArea := areaIdentity.trans area
  have actual := estimate (diskPhysicalSpectralCoordinate data) tube.le actualArea
  change diskPhysicalSpectralChart (diskPhysicalSpectralCoordinate data) = data at rightInverse
  rwa [rightInverse] at actual

end EulerNonuniqueness.Paper
