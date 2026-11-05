import EulerNonuniqueness.Section4.ReferenceDeformationScale

noncomputable section

namespace EulerNonuniqueness.Paper

open scoped BigOperators

private theorem remove_reference_shape_weight {length residual bound : ℝ} (positive : 0 < length)
    (estimate : (30 / length) * residual ≤ bound) : residual ≤ (length / 30) * bound := by
  have multiplied := mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ length / 30)
  have cancellation : length / 30 * (30 / length * residual) = residual := by
    field_simp [positive.ne']
    <;> ring
  rwa [cancellation] at multiplied

theorem Scales.reference_center_deformation_cost_le {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) {deformation bound : ℝ} (deformationNonnegative : 0 ≤ deformation)
    (boundNonnegative : 0 ≤ bound)
    (deformationBound : deformation ≤ bound / scales.omega (index.val + 1) ^ 2)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1) :
    3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * (scales.length (index.val + 1) / 100) ^ 3) +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) /
          (|scales.location (index.val + 1) - scales.location (source.val + 1)| / 8) ^ 3 ≤
    ((13824000000 + 113246208 / Real.pi) * bound / scales.amplitude) *
      (scales.length (index.val + 1) / scales.omega (index.val + 1) ^ 4) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have internalBound := scales.reference_internal_deformation_cost_le amplitudePositive frequencyPositive
    ratioPositive (index.val + 1) deformationBound
  have externalBound := scales.reference_external_deformation_cost_fourth_le amplitudePositive frequencyBound
    ratioBound alphaPositive index deformationNonnegative boundNonnegative deformationBound lengthBound hessianBound
  have estimate := add_le_add internalBound externalBound
  rw [← mul_add] at estimate
  exact (remove_reference_shape_weight (scales.length_pos (index.val + 1)) estimate).trans_eq (by ring)

end EulerNonuniqueness.Paper
