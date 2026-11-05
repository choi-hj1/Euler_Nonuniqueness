import EulerNonuniqueness.Section6.ReceiverSourceVelocityBound
import EulerNonuniqueness.Section6.ExteriorInversePowerBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem receiver_transport_coefficient_point_bound {source receiver : Vorticity}
    (receiverIntegrable : Integrable receiver) (center : ℂ) {radius distance : ℝ}
    (supported : Function.support receiver ⊆ Metric.closedBall center radius)
    (positive : 0 < distance) (small : 2 * radius ≤ distance)
    (separated : ∀ position ∈ Function.support source, distance ≤ ‖center - position‖)
    (power : ℕ) (position : ℂ) :
    ‖source position • (star (biotSavart receiver position) *
      (star (center - position))⁻¹ ^ (power + 3))‖ ≤
      ((∫ location, |receiver location|) / Real.pi * distance⁻¹ ^ (power + 2)) *
        inverseSquareVorticityWeight source center position := by
  by_cases zero : source position = 0
  · simp [zero, inverseSquareVorticityWeight]
  have lower := separated position (Function.mem_support.mpr zero)
  have normPositive : 0 < ‖center - position‖ := positive.trans_le lower
  have distinct : position ≠ center := by
    intro equal
    simp [equal] at normPositive
  have velocity := norm_receiver_biotSavart_le receiverIntegrable center position supported
    (by rw [norm_sub_rev]; exact small.trans lower) distinct
  rw [norm_sub_rev position center] at velocity
  have massNonnegative : 0 ≤ ∫ location, |receiver location| := integral_nonneg fun _ => abs_nonneg _
  rw [norm_smul, Real.norm_eq_abs, norm_mul, norm_star, norm_pow, norm_inv, norm_star]
  have inverseBound := inv_anti₀ positive lower
  have radial := pow_le_pow_left₀ (inv_nonneg.mpr normPositive.le) inverseBound (power + 2)
  calc
    _ ≤ |source position| * (((∫ location, |receiver location|) / (Real.pi * ‖center - position‖)) *
        ‖center - position‖⁻¹ ^ (power + 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right velocity (by positivity)) (abs_nonneg _)
    _ = ((∫ location, |receiver location|) / Real.pi) *
        ‖center - position‖⁻¹ ^ (power + 2) *
        (|source position| * ‖center - position‖⁻¹ ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev, pow_add, pow_succ]
      ring
    _ ≤ _ := by
      unfold inverseSquareVorticityWeight
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left radial (div_nonneg massNonnegative Real.pi_pos.le)) (by positivity)

theorem integrable_receiver_transport_coefficient {source receiver : Vorticity}
    (sourceIntegrable : Integrable source) (receiverIntegrable : Integrable receiver)
    (center : ℂ) {radius distance : ℝ}
    (supported : Function.support receiver ⊆ Metric.closedBall center radius)
    (positive : 0 < distance) (small : 2 * radius ≤ distance)
    (separated : ∀ position ∈ Function.support source, distance ≤ ‖center - position‖)
    (power : ℕ) :
    Integrable (fun position : ℂ => source position • (star (biotSavart receiver position) *
      (star (center - position))⁻¹ ^ (power + 3))) := by
  have weight := integrable_inverseSquareVorticityWeight sourceIntegrable center positive separated
  have conjugateContinuous : Continuous (star : ℂ → ℂ) := by fun_prop
  have velocity := conjugateContinuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_biotSavart receiverIntegrable.aestronglyMeasurable)
  have kernelMeasurable : Measurable (fun position : ℂ => (star (center - position))⁻¹ ^ (power + 3)) := by
    fun_prop
  exact (weight.const_mul ((∫ location, |receiver location|) / Real.pi * distance⁻¹ ^ (power + 2))).mono'
    (sourceIntegrable.aestronglyMeasurable.smul (velocity.mul kernelMeasurable.aestronglyMeasurable))
    (Filter.Eventually.of_forall (receiver_transport_coefficient_point_bound receiverIntegrable center
      supported positive small separated power))

theorem norm_integral_receiver_transport_coefficient_le {source receiver : Vorticity}
    (sourceIntegrable : Integrable source) (receiverIntegrable : Integrable receiver)
    (center : ℂ) {radius distance : ℝ}
    (supported : Function.support receiver ⊆ Metric.closedBall center radius)
    (positive : 0 < distance) (small : 2 * radius ≤ distance)
    (separated : ∀ position ∈ Function.support source, distance ≤ ‖center - position‖)
    (power : ℕ) :
    ‖∫ position : ℂ, source position • (star (biotSavart receiver position) *
      (star (center - position))⁻¹ ^ (power + 3))‖ ≤
      ((∫ location, |receiver location|) / Real.pi * distance⁻¹ ^ (power + 2)) *
        ∫ position, inverseSquareVorticityWeight source center position := by
  have estimate := norm_integral_le_of_norm_le
    ((integrable_inverseSquareVorticityWeight sourceIntegrable center positive separated).const_mul
      ((∫ location, |receiver location|) / Real.pi * distance⁻¹ ^ (power + 2)))
    (Filter.Eventually.of_forall (receiver_transport_coefficient_point_bound receiverIntegrable center
      supported positive small separated power))
  simpa only [integral_const_mul] using estimate

end EulerNonuniqueness.Section6
