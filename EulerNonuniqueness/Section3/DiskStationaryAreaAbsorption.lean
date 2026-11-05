import EulerNonuniqueness.Section3.DiskStationaryAreaUniformFactor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance areaAbsorptionHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance areaAbsorptionC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem norm_diskAreaMeanComponent_le (mean : ℝ) :
    ‖c1Product standardCircleBanach (c1Constant (mean : ℂ))‖ ≤
      (8 * ‖standardCircleBanach‖) * |mean| := by
  have constantBound := c1Constant_norm_bound (mean : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at constantBound
  exact (c1Product_norm_bound standardCircleBanach (c1Constant (mean : ℂ))).trans
    (mul_le_mul_of_nonneg_left constantBound (by positivity : 0 ≤ 8 * ‖standardCircleBanach‖))

theorem diskStationaryArea_exists_transverse_norm_absorption :
    ∃ radius > 0, ∀ increment : PeriodicC1HolderHalf,
      ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖ ≤ radius →
      diskStationaryArea increment = Real.pi →
      ‖increment - diskRelabelNeutralCLM increment‖ ≤ 2 * ‖diskPhysicalTransverseProjection increment‖ := by
  obtain ⟨radius, positive, constant, constantNonnegative, meanEstimate⟩ :=
    diskStationaryArea_exists_relabel_factored_mean_bound
  let coefficient := 8 * ‖standardCircleBanach‖
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have productNonnegative : 0 ≤ coefficient * constant := mul_nonneg coefficientNonnegative constantNonnegative
  have tinyPositive : 0 < 1 / (2 * (coefficient * constant + 1)) := by positivity
  have tinyBound : (coefficient * constant) * (1 / (2 * (coefficient * constant + 1))) ≤ 1 / 2 := by
    rw [show (coefficient * constant) * (1 / (2 * (coefficient * constant + 1))) =
      (coefficient * constant) / (2 * (coefficient * constant + 1)) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (coefficient * constant + 1))).mpr
    nlinarith
  refine ⟨min radius (1 / (2 * (coefficient * constant + 1))), lt_min positive tinyPositive, ?_⟩
  intro increment inside area
  let size := ‖diskRelabelNeutralCLM increment‖ + ‖increment - diskRelabelNeutralCLM increment‖
  have mean := meanEstimate increment (inside.trans (min_le_left _ _)) area
  have small : coefficient * constant * size ≤ 1 / 2 := by
    apply (mul_le_mul_of_nonneg_left (inside.trans (min_le_right _ _)) productNonnegative).trans
    exact tinyBound
  have difference : ‖increment - diskRelabelNeutralCLM increment‖ ≤
      ‖diskPhysicalTransverseProjection increment‖ + coefficient * |diskRadialMean increment| := by
    rw [diskPhysical_relabel_neutral_decomposition]
    exact (norm_add_le _ _).trans
      (add_le_add_left (norm_diskAreaMeanComponent_le (diskRadialMean increment)) _)
  have absorbed : ‖increment - diskRelabelNeutralCLM increment‖ ≤
      ‖diskPhysicalTransverseProjection increment‖ + (1 / 2 : ℝ) * ‖increment - diskRelabelNeutralCLM increment‖ := by
    calc
      _ ≤ ‖diskPhysicalTransverseProjection increment‖ + coefficient * |diskRadialMean increment| := difference
      _ ≤ ‖diskPhysicalTransverseProjection increment‖ +
          coefficient * (constant * size * ‖increment - diskRelabelNeutralCLM increment‖) :=
        add_le_add_left (mul_le_mul_of_nonneg_left mean coefficientNonnegative) _
      _ = ‖diskPhysicalTransverseProjection increment‖ +
          (coefficient * constant * size) * ‖increment - diskRelabelNeutralCLM increment‖ := by ring
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right small (norm_nonneg _)) _
  linarith

end

end EulerNonuniqueness.Paper
