import EulerNonuniqueness.Section3.HolderBanachAlgebra
import EulerNonuniqueness.Section3.ContourCauchyOperator

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem PeriodicC1HolderHalf.tangent_lower_bound (data : PeriodicC1HolderHalf) (label : ℝ) :
    1 - ‖data - standardCircleBanach‖ ≤ ‖data.val.2.val.1 label‖ := by
  have triangle := norm_add_le (standardCircleTangent label - data.val.2.val.1 label) (data.val.2.val.1 label)
  rw [sub_add_cancel, standardCircleTangent_norm,
    norm_sub_rev (standardCircleTangent label) (data.val.2.val.1 label)] at triangle
  linarith [PeriodicC1HolderHalf.derivative_close_circle data label]

noncomputable def contourTangentQuotient (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicHolderHalf :=
  holderProduct (holderConjugate data.val.2)
    (holderInverse data.val.2 (sub_pos.mpr (small.trans_le (min_le_left _ _)))
      (PeriodicC1HolderHalf.tangent_lower_bound data))

theorem contourTangentQuotient_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    (contourTangentQuotient data small).val.1 label = star (data.val.2.val.1 label) / data.val.2.val.1 label := by
  rw [contourTangentQuotient, holderProduct_value, holderConjugate_value, holderInverse_value, div_eq_mul_inv]

theorem PeriodicC1HolderHalf.tangent_ne_zero (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    data.val.2.val.1 label ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt ((sub_pos.mpr (small.trans_le (min_le_left _ _))).trans_le
    (PeriodicC1HolderHalf.tangent_lower_bound data label)))

end EulerNonuniqueness.Paper
