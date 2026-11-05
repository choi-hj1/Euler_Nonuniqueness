import EulerNonuniqueness.Section3.ContourAntiholomorphicFunctionalAlgebra
import EulerNonuniqueness.Section3.ContourInversePowerSeparation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def normalizedExteriorInversePowerKernel (parameter : ℂ) (power : ℕ) (position : ℂ) : ℂ :=
  (star (1 - parameter * position))⁻¹ ^ (power + 1) - 1

theorem conjugate_inverse_power_normalization (displacement scale position : ℂ)
    (nonzero : displacement ≠ 0) (power : ℕ) :
    (star (displacement - scale * position))⁻¹ ^ (power + 1) =
      (star displacement)⁻¹ ^ (power + 1) *
        (normalizedExteriorInversePowerKernel (scale / displacement) power position + 1) := by
  have identity : displacement - scale * position = displacement * (1 - scale / displacement * position) := by
    field_simp
    <;> ring
  rw [identity]
  simp only [normalizedExteriorInversePowerKernel, sub_add_cancel, star_mul, mul_inv_rev, mul_pow]
  <;> ring

theorem normalizedExteriorInversePowerKernel_continuous_comp
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (displacement scale : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : 2 * ‖scale‖ + distance ≤ ‖displacement‖) (power : ℕ) :
    Continuous (fun label => normalizedExteriorInversePowerKernel (scale / displacement) power (data.val.1 label)) := by
  have nonzero : displacement ≠ 0 := norm_pos_iff.mp (by linarith [norm_nonneg scale])
  unfold normalizedExteriorInversePowerKernel
  apply Continuous.sub _ continuous_const
  apply Continuous.pow
  apply Continuous.inv₀
  · exact (continuous_const.sub (continuous_const.mul data.val.1.continuous)).star
  · intro label
    apply star_ne_zero.mpr
    have actual : displacement - scale * data.val.1 label ≠ 0 :=
      norm_pos_iff.mp (positive.trans_le (norm_displacement_sub_mul_lower
        (nearCircle_value_norm_lt_two data small label).le separated))
    intro zero
    apply actual
    have identity : displacement - scale * data.val.1 label =
        displacement * (1 - scale / displacement * data.val.1 label) := by
      field_simp
      <;> ring
    rw [identity, zero, mul_zero]

theorem contourAntiholomorphicFunctional_inverse_power_normalization
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (displacement scale : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : 2 * ‖scale‖ + distance ≤ ‖displacement‖) (power : ℕ) :
    contourAntiholomorphicFunctional
        (fun position => (star (displacement - scale * position))⁻¹ ^ (power + 1)) data =
      (star displacement)⁻¹ ^ (power + 1) *
        (contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel (scale / displacement) power) data +
          (contourAreaFunctional data : ℂ)) := by
  have nonzero : displacement ≠ 0 := norm_pos_iff.mp (by linarith [norm_nonneg scale])
  have identity : (fun position => (star (displacement - scale * position))⁻¹ ^ (power + 1)) =
      fun position => (star displacement)⁻¹ ^ (power + 1) *
        (normalizedExteriorInversePowerKernel (scale / displacement) power position + 1) :=
    funext fun position => conjugate_inverse_power_normalization displacement scale position nonzero power
  rw [identity, contourAntiholomorphicFunctional_mul_const,
    contourAntiholomorphicFunctional_add_const data _ 1
      (normalizedExteriorInversePowerKernel_continuous_comp data small displacement scale positive separated power),
    one_mul]

end EulerNonuniqueness.Paper
