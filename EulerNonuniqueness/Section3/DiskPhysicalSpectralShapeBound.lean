import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelabelDefect

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] physicalSpectralRelabelDefectC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralChart_exists_uniform_area_shape_bound :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ point : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM point‖ + ‖point - diskRelabelNeutralCLM point‖ ≤ radius →
      diskSpectralTubularArea point = Real.pi →
      ‖diskPhysicalSpectralChart point - standardCircleBanach‖ ≤
        constant * (‖diskRelabelNeutralCLM point‖ + ‖diskPhysicalTransverseProjection point‖) := by
  obtain ⟨chartRadius, chartPositive, constant, one, chartBound, _⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  obtain ⟨areaRadius, areaPositive, _, _, absorption⟩ :=
    diskSpectralTubularArea_exists_transverse_absorption
  refine ⟨min chartRadius areaRadius, lt_min chartPositive areaPositive,
    2 * constant, by linarith, ?_⟩
  intro point small area
  have pointIdentity : diskRelabelNeutralCLM point + (point - diskRelabelNeutralCLM point) = point := by abel
  have pointNorm := norm_add_le (diskRelabelNeutralCLM point) (point - diskRelabelNeutralCLM point)
  rw [pointIdentity] at pointNorm
  have pointBound := pointNorm.trans (small.trans (min_le_left _ _))
  have absorbed := (absorption point (small.trans (min_le_right _ _)) area).1
  rw [diskSpectralRelative_transverse] at absorbed
  have total := pointNorm.trans (add_le_add_left absorbed ‖diskRelabelNeutralCLM point‖)
  have actual := (chartBound point pointBound).1.trans
    (mul_le_mul_of_nonneg_left total (by linarith : 0 ≤ constant))
  exact actual.trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ constant) (norm_nonneg (diskRelabelNeutralCLM point))])

theorem diskPhysicalSpectralCoordinate_exists_uniform_area_shape_bound :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ data : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ < radius → contourAreaFunctional data = Real.pi →
      ‖data - standardCircleBanach‖ ≤ constant *
        (‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ +
          ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖) := by
  obtain ⟨tubeRadius, tubePositive, constant, one, estimate⟩ :=
    diskPhysicalSpectralChart_exists_uniform_area_shape_bound
  obtain ⟨radius, positive, coordinates⟩ := diskPhysicalSpectralCoordinate_exists_radius tubePositive
  refine ⟨radius, positive, constant, one, ?_⟩
  intro data small area
  obtain ⟨rightInverse, areaIdentity, tube, _⟩ := coordinates data small
  have actual := estimate (diskPhysicalSpectralCoordinate data) tube.le (areaIdentity.trans area)
  change diskPhysicalSpectralChart (diskPhysicalSpectralCoordinate data) = data at rightInverse
  rwa [rightInverse] at actual

end EulerNonuniqueness.Paper
