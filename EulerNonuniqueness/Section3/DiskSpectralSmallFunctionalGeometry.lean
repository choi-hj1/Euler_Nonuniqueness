import EulerNonuniqueness.Section3.DiskSpectralFunctionalPairGeometry

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] spectralFunctionalGeometryC1Group spectralFunctionalGeometryC1Space

theorem diskPhysicalSpectral_exists_small_functional_pair_geometry :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskNeutralCLM initial‖ < 1 / 2 ∧ ‖diskNeutralCLM final‖ < 1 / 2 ∧
      ‖diskStationaryChart (diskRelabelNeutralCLM initial)‖ +
        (‖diskPhysicalSpectralDefect initial‖ + ‖diskPhysicalSpectralDefect final‖) ≤ 5 / 2 ∧
      ‖diskStationaryChart (diskRelabelNeutralCLM final)‖ +
        (‖diskPhysicalSpectralDefect initial‖ + ‖diskPhysicalSpectralDefect final‖) ≤ 5 / 2 ∧
      ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖ +
        ‖diskStationaryChart (diskRelabelNeutralCLM initial) - diskStationaryChart (diskRelabelNeutralCLM final)‖ *
          ‖diskPhysicalSpectralDefect final‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨geometryRadius, geometryPositive, constant, nonnegative, bound⟩ :=
    diskPhysicalSpectral_exists_functional_pair_geometry
  obtain ⟨domainRadius, domainPositive, domain⟩ :=
    movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1 / 6)
  refine ⟨min geometryRadius domainRadius, by positivity, constant, nonnegative, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  have actual := bound initial final (ball_subset_ball (min_le_left _ _) initialInside)
    (ball_subset_ball (min_le_left _ _) finalInside) initialArea finalArea
  have initialDomain := domain initial (ball_subset_ball (min_le_right _ _) initialInside)
  have finalDomain := domain final (ball_subset_ball (min_le_right _ _) finalInside)
  have initialBase : ‖diskStationaryChart (diskRelabelNeutralCLM initial)‖ ≤ 13 / 6 := by
    have triangle := norm_add_le (diskStationaryChart (diskRelabelNeutralCLM initial) - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [initialDomain.2.2.1, standardCircleBanach_norm_bound]
  have finalBase : ‖diskStationaryChart (diskRelabelNeutralCLM final)‖ ≤ 13 / 6 := by
    have triangle := norm_add_le (diskStationaryChart (diskRelabelNeutralCLM final) - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel] at triangle
    linarith [finalDomain.2.2.1, standardCircleBanach_norm_bound]
  exact ⟨actual.1, actual.2.1, by linarith [initialDomain.2.2.2, finalDomain.2.2.2],
    by linarith [initialDomain.2.2.2, finalDomain.2.2.2], actual.2.2.2.2⟩

end EulerNonuniqueness.Paper
