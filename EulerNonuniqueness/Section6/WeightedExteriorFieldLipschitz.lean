import EulerNonuniqueness.Section6.ExteriorInversePowerBound
import EulerNonuniqueness.Section6.PatchExternalCentroidLaw

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Section6

theorem weighted_exterior_kernel_difference {center position source : ℂ} {distance : ℝ}
    (positive : 0 < distance) (separated : distance ≤ ‖center - source‖)
    (nearby : ‖position - center‖ ≤ distance / 2) :
    ‖biotSavartKernel (position - source) - biotSavartKernel (center - source)‖ ≤
      (‖position - center‖ / Real.pi) * ‖center - source‖⁻¹ ^ 2 := by
  have centerPositive : 0 < ‖center - source‖ := positive.trans_le separated
  have triangle := norm_add_le (center - position) (position - source)
  rw [sub_add_sub_cancel, norm_sub_rev center position] at triangle
  have lower : ‖center - source‖ / 2 ≤ ‖position - source‖ := by linarith
  have positionPositive : 0 < ‖position - source‖ := by linarith
  rw [norm_biotSavartKernel_sub (norm_pos_iff.mp positionPositive) (norm_pos_iff.mp centerPositive)]
  have difference : position - source - (center - source) = position - center := by abel
  rw [difference]
  have estimate : ‖position - center‖ / (2 * Real.pi * ‖position - source‖ * ‖center - source‖) ≤
      ‖position - center‖ / (Real.pi * ‖center - source‖ ^ 2) := by
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right lower (mul_nonneg Real.pi_pos.le centerPositive.le)]
  exact estimate.trans_eq (by simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]; ring)

theorem weighted_exterior_biotSavart_difference {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center position : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (nearby : ‖position - center‖ ≤ distance / 2) :
    ‖biotSavart vorticity position - biotSavart vorticity center‖ ≤
      (‖position - center‖ / Real.pi) * ∫ source, inverseSquareVorticityWeight vorticity center source := by
  rw [biotSavart, biotSavart, ← integral_sub
    (integrable_biotSavart_integrand_of_L1_L4 integrable membership position)
    (integrable_biotSavart_integrand_of_L1_L4 integrable membership center)]
  have estimate := norm_integral_le_of_norm_le
    (f := fun source => vorticity source • biotSavartKernel (position - source) -
      vorticity source • biotSavartKernel (center - source))
    ((integrable_inverseSquareVorticityWeight integrable center positive separated).const_mul
      (‖position - center‖ / Real.pi)) (Filter.Eventually.of_forall fun source => by
        dsimp only
        by_cases zero : vorticity source = 0
        · simp [zero, inverseSquareVorticityWeight]
        rw [← smul_sub, norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left
          (weighted_exterior_kernel_difference positive (separated source (Function.mem_support.mpr zero)) nearby)
          (abs_nonneg _)).trans_eq (by unfold inverseSquareVorticityWeight; ring))
  simpa only [integral_const_mul] using estimate

theorem weighted_exterior_centroid_average_defect {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center : ℂ) {domain : Set ℂ} (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (areaPositive : 0 < volume.real domain) {radius distance : ℝ}
    (positive : 0 < distance) (small : radius ≤ distance / 2)
    (contained : domain ⊆ Metric.closedBall center radius)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖) :
    ‖(volume.real domain)⁻¹ • (∫ position in domain,
      biotSavart vorticity position - biotSavart vorticity center)‖ ≤
      (radius / Real.pi) * ∫ source, inverseSquareVorticityWeight vorticity center source := by
  have weightNonnegative : 0 ≤ ∫ source, inverseSquareVorticityWeight vorticity center source :=
    integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have estimate := norm_setIntegral_le_of_norm_le_const_ae finite (by
    filter_upwards [ae_restrict_mem measurable] with position member
    have localBound : ‖position - center‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using contained member
    exact (weighted_exterior_biotSavart_difference integrable membership center position positive separated
      (localBound.trans small)).trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right localBound Real.pi_pos.le) weightNonnegative))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr areaPositive)]
  have scaled := mul_le_mul_of_nonneg_left estimate (inv_nonneg.mpr areaPositive.le)
  exact scaled.trans_eq (by field_simp)

end EulerNonuniqueness.Section6
