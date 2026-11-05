import EulerNonuniqueness.Section3.HolderBanachAlgebraNorms
import EulerNonuniqueness.Section3.ContourCauchyOperatorLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourTangentInverse (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicHolderHalf :=
  holderInverse data.val.2 (sub_pos.mpr (small.trans_le (min_le_left _ _)))
    (PeriodicC1HolderHalf.tangent_lower_bound data)

def contourTangentInverseConstant (radius : ℝ) : ℝ := max (1 / (1 - radius)) ((radius + 2) / (1 - radius) ^ 2)

theorem contourTangentInverseConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourTangentInverseConstant radius := by
  have lower_pos := sub_pos.mpr (radius_small.trans_le (min_le_left _ _))
  unfold contourTangentInverseConstant
  positivity

theorem contourTangentInverse_uniform_norm_bound (data : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourTangentInverse data (nearby.trans_lt radius_small)‖ ≤ contourTangentInverseConstant radius := by
  have lower_pos : 0 < 1 - radius := sub_pos.mpr (radius_small.trans_le (min_le_left _ _))
  have separated : ∀ label : ℝ, 1 - radius ≤ ‖data.val.2.val.1 label‖ := by
    intro label
    exact (sub_le_sub_left nearby 1).trans (PeriodicC1HolderHalf.tangent_lower_bound data label)
  have identity : contourTangentInverse data (nearby.trans_lt radius_small) = holderInverse data.val.2 lower_pos separated := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact (holderInverse_norm_bound data.val.2 lower_pos separated).trans
    (max_le_max le_rfl (div_le_div_of_nonneg_right
      ((PeriodicC1HolderHalf.tangent_norm_bound data).trans (PeriodicC1HolderHalf.norm_le_radius_add_two data nearby))
      (sq_nonneg _)))

theorem contourTangentInverse_parameter_norm_bound (first second : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius) (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourTangentInverse first (first_near.trans_lt radius_small) -
      contourTangentInverse second (second_near.trans_lt radius_small)‖ ≤
      4 * ‖first - second‖ * contourTangentInverseConstant radius ^ 2 := by
  have inverse_nonneg := contourTangentInverseConstant_nonneg radius_nonneg radius_small
  have actual := holderInverse_difference_norm_bound first.val.2 second.val.2
    (sub_pos.mpr ((first_near.trans_lt radius_small).trans_le (min_le_left _ _)))
    (sub_pos.mpr ((second_near.trans_lt radius_small).trans_le (min_le_left _ _)))
    (PeriodicC1HolderHalf.tangent_lower_bound first) (PeriodicC1HolderHalf.tangent_lower_bound second)
  change ‖contourTangentInverse first (first_near.trans_lt radius_small) -
      contourTangentInverse second (second_near.trans_lt radius_small)‖ ≤
      4 * ‖first.val.2 - second.val.2‖ * ‖contourTangentInverse first (first_near.trans_lt radius_small)‖ *
        ‖contourTangentInverse second (second_near.trans_lt radius_small)‖ at actual
  calc
    _ ≤ 4 * ‖first.val.2 - second.val.2‖ * ‖contourTangentInverse first (first_near.trans_lt radius_small)‖ *
        ‖contourTangentInverse second (second_near.trans_lt radius_small)‖ := actual
    _ ≤ 4 * ‖first - second‖ * contourTangentInverseConstant radius * contourTangentInverseConstant radius := by
      gcongr
      · exact PeriodicC1HolderHalf.tangent_difference_norm_bound first second
      · exact contourTangentInverse_uniform_norm_bound first radius_nonneg radius_small first_near
      · exact contourTangentInverse_uniform_norm_bound second radius_nonneg radius_small second_near
    _ = _ := by ring

def contourTangentQuotientConstant (radius : ℝ) : ℝ := 2 * (radius + 2) * contourTangentInverseConstant radius

def contourTangentQuotientLipschitzConstant (radius : ℝ) : ℝ :=
  2 * contourTangentInverseConstant radius + 8 * (radius + 2) * contourTangentInverseConstant radius ^ 2

theorem contourTangentQuotient_uniform_norm_bound (data : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourTangentQuotient data (nearby.trans_lt radius_small)‖ ≤ contourTangentQuotientConstant radius := by
  have inverse_nonneg := contourTangentInverseConstant_nonneg radius_nonneg radius_small
  change ‖holderProduct (holderConjugate data.val.2) (contourTangentInverse data (nearby.trans_lt radius_small))‖ ≤ _
  apply (holderProduct_norm_bound _ _).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left ((holderConjugate_norm_bound data.val.2).trans
      ((PeriodicC1HolderHalf.tangent_norm_bound data).trans (PeriodicC1HolderHalf.norm_le_radius_add_two data nearby))) (by norm_num))
    (contourTangentInverse_uniform_norm_bound data radius_nonneg radius_small nearby)
    (norm_nonneg _) (by linarith)

theorem contourTangentQuotient_parameter_norm_bound (first second : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius) (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourTangentQuotient first (first_near.trans_lt radius_small) -
      contourTangentQuotient second (second_near.trans_lt radius_small)‖ ≤
      contourTangentQuotientLipschitzConstant radius * ‖first - second‖ := by
  have inverse_nonneg := contourTangentInverseConstant_nonneg radius_nonneg radius_small
  change ‖holderProduct (holderConjugate first.val.2) (contourTangentInverse first (first_near.trans_lt radius_small)) -
    holderProduct (holderConjugate second.val.2) (contourTangentInverse second (second_near.trans_lt radius_small))‖ ≤ _
  apply (holderProduct_difference_norm_bound _ _ _ _).trans
  calc
    _ ≤ 2 * ‖first - second‖ * contourTangentInverseConstant radius +
        2 * (radius + 2) * (4 * ‖first - second‖ * contourTangentInverseConstant radius ^ 2) := by
      gcongr
      · exact (holderConjugate_difference_norm_bound first.val.2 second.val.2).trans
          (PeriodicC1HolderHalf.tangent_difference_norm_bound first second)
      · exact contourTangentInverse_uniform_norm_bound first radius_nonneg radius_small first_near
      · exact (holderConjugate_norm_bound second.val.2).trans
          ((PeriodicC1HolderHalf.tangent_norm_bound second).trans (PeriodicC1HolderHalf.norm_le_radius_add_two second second_near))
      · exact contourTangentInverse_parameter_norm_bound first second radius_nonneg radius_small first_near second_near
    _ = _ := by unfold contourTangentQuotientLipschitzConstant; ring

end

end EulerNonuniqueness.Paper
