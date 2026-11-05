import EulerNonuniqueness.Section3.DomainBiotSavartLimit
import EulerNonuniqueness.Section3.AffineContourSelfVelocity

open Set MeasureTheory Filter

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem integral_nearCircleInterior_biotSavart_boundary
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    (∫ position in nearCircleInterior data small, biotSavartKernel (data.val.1 target - position)) =
      contourVelocity data.val.1 data.val.2.val.1 target (-Real.pi) Real.pi := by
  have ordered : target - Real.pi ≤ target + Real.pi := by linarith [Real.pi_pos]
  let chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖
  have chord_positive : 0 < chord := sub_pos.mpr chord_small
  have chord_bound : ∀ source ∈ Icc (target - Real.pi) (target + Real.pi),
      chord * |source - target| ≤ ‖data.val.1 source - data.val.1 target‖ := by
    intro source source_mem
    have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [source_mem.1, source_mem.2, Real.pi_pos]
    have estimate := PeriodicC1HolderHalf.chord_bound_extended data nearby
    rwa [norm_sub_rev] at estimate
  have log_integrable := contour_log_integrable_interval ordered
    (show target ∈ Icc (target - Real.pi) (target + Real.pi) by constructor <;> linarith [Real.pi_pos])
    (show 0 < ‖data‖ + 1 by positivity) chord_positive data.val.1.continuous data.val.2.val.1.continuous
    (fun source _ => PeriodicC1HolderHalf.hasDerivAt data source)
    (fun source _ => (PeriodicC1HolderHalf.speed_bound data source).trans (by linarith)) chord_bound
  have distinct_ae : ∀ᵐ source : ℝ ∂volume, source ≠ target := by
    rw [ae_iff]
    simp
  have nonzero : ∀ᵐ source ∂(volume.restrict (uIoc (target - Real.pi) (target + Real.pi))),
      data.val.1 source ≠ data.val.1 target := by
    filter_upwards [ae_restrict_of_ae distinct_ae,
      ae_restrict_mem measurableSet_uIoc] with source distinct source_mem
    rw [uIoc_of_le ordered] at source_mem
    apply sub_ne_zero.mp
    apply norm_pos_iff.mp
    exact (mul_pos chord_positive (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
      (chord_bound source ⟨source_mem.1.le, source_mem.2⟩)
  rw [integral_nearCircleInterior_biotSavart_window_of_log_integrable data small
    (data.val.1 target) target nonzero log_integrable, periodicContourVelocity_centered data]
  unfold contourVelocity
  rw [one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro source _
  dsimp only
  rw [norm_sub_rev]

end

end EulerNonuniqueness.Paper
