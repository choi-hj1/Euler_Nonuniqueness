import EulerNonuniqueness.Section3.ContourMomentSpectralRelative

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem contourPolynomialMoment_exists_spectral_absolute_ball :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ state : PeriodicC1HolderHalf, state ∈ ball 0 radius → diskSpectralTubularArea state = Real.pi →
      ∀ degree : ℕ, ‖contourPolynomialMoment (degree + 1) (diskPhysicalSpectralChart state)‖ ≤
        constant * (96 : ℝ) ^ (degree + 1) * ‖diskPhysicalTransverseProjection state‖ := by
  obtain ⟨relativeRadius, relativePositive, constant, nonnegative, bound⟩ :=
    contourPolynomialMoment_exists_spectral_relative_ball
  obtain ⟨domainRadius, domainPositive, domain⟩ :=
    movingStrainSpectral_exists_relabel_domain (by norm_num : (0 : ℝ) < 1 / 6)
  refine ⟨min relativeRadius domainRadius, by positivity, 2 * constant, by positivity, ?_⟩
  intro state inside area degree
  have zeroInside : (0 : PeriodicC1HolderHalf) ∈ ball 0 relativeRadius := mem_ball_zero_iff.mpr (by simpa using relativePositive)
  have zeroArea : diskSpectralTubularArea (0 : PeriodicC1HolderHalf) = Real.pi := by
    rw [diskSpectralTubularArea, diskSpectralTubularChart_zero, diskStationaryArea_zero]
  have actual := bound state 0 (ball_subset_ball (min_le_left _ _) inside) zeroInside area zeroArea degree
  simp only [diskPhysicalSpectralChart_zero, contourPolynomialMoment_circle_positive, sub_zero,
    map_zero, norm_zero, add_zero] at actual
  have neutralSmall := (domain state (ball_subset_ball (min_le_right _ _) inside)).1
  have budget : ‖diskPhysicalTransverseProjection state‖ +
      ‖diskPhysicalTransverseProjection state‖ * ‖diskNeutralCLM state‖ ≤ 2 * ‖diskPhysicalTransverseProjection state‖ := by
    nlinarith [norm_nonneg (diskPhysicalTransverseProjection state)]
  exact actual.trans ((mul_le_mul_of_nonneg_left budget (by positivity)).trans_eq (by ring))

end EulerNonuniqueness.Paper
