import EulerNonuniqueness.Section3.HolderDifferentialAlgebra

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def holderInverseQuadratic (data increment : PeriodicHolderHalf) : PeriodicHolderHalf :=
  holderProduct increment (holderProduct increment (holderProduct (extendedHolderInverse data)
    (holderProduct (extendedHolderInverse data) (extendedHolderInverse data))))

theorem holderInverse_cubic_remainder_identity (data increment : PeriodicHolderHalf)
    {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (small : ‖increment‖ ≤ lower / 2) :
    extendedHolderInverse (data + increment) - extendedHolderInverse data -
        holderInverseDerivativeCLM data increment - holderInverseQuadratic data increment =
      -holderProduct increment (holderProduct increment (holderProduct increment
        (holderProduct (extendedHolderInverse (data + increment))
          (holderProduct (extendedHolderInverse data)
            (holderProduct (extendedHolderInverse data) (extendedHolderInverse data)))))) := by
  have next_separated := holder_perturbation_separated data increment separated small
  have half_positive : 0 < lower / 2 := by linarith
  have derivative_apply : holderInverseDerivativeCLM data increment =
      -holderProduct (extendedHolderInverse data)
        (holderProduct increment (extendedHolderInverse data)) := rfl
  rw [derivative_apply]
  unfold holderInverseQuadratic
  rw [extendedHolderInverse_eq data positive separated,
    extendedHolderInverse_eq (data + increment) half_positive next_separated]
  apply PeriodicHolderHalf.ext_value
  intro label
  have first_ne := norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le (separated label)))
  have second_ne := norm_ne_zero_iff.mp (ne_of_gt (half_positive.trans_le (next_separated label)))
  change data.val.1 label + increment.val.1 label ≠ 0 at second_ne
  change (data.val.1 label + increment.val.1 label)⁻¹ - (data.val.1 label)⁻¹ -
      (-((data.val.1 label)⁻¹ * (increment.val.1 label * (data.val.1 label)⁻¹))) -
      increment.val.1 label * (increment.val.1 label * ((data.val.1 label)⁻¹ *
        ((data.val.1 label)⁻¹ * (data.val.1 label)⁻¹))) =
    -(increment.val.1 label * (increment.val.1 label * (increment.val.1 label *
      ((data.val.1 label + increment.val.1 label)⁻¹ * ((data.val.1 label)⁻¹ *
        ((data.val.1 label)⁻¹ * (data.val.1 label)⁻¹))))))
  field_simp [first_ne, second_ne]
  ring

theorem holderInverse_cubic_remainder_norm (data increment : PeriodicHolderHalf)
    {lower bound : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (small : ‖increment‖ ≤ lower / 2)
    (bound_nonnegative : 0 ≤ bound) (first_bound : ‖extendedHolderInverse data‖ ≤ bound)
    (second_bound : ‖extendedHolderInverse (data + increment)‖ ≤ bound) :
    ‖extendedHolderInverse (data + increment) - extendedHolderInverse data -
      holderInverseDerivativeCLM data increment - holderInverseQuadratic data increment‖ ≤
      (64 * bound ^ 4) * ‖increment‖ ^ 3 := by
  rw [holderInverse_cubic_remainder_identity data increment positive separated small, norm_neg]
  calc
    _ ≤ 2 * ‖increment‖ *
        (2 * ‖increment‖ * (2 * ‖increment‖ *
          (2 * ‖extendedHolderInverse (data + increment)‖ *
            (2 * ‖extendedHolderInverse data‖ *
              (2 * ‖extendedHolderInverse data‖ * ‖extendedHolderInverse data‖))))) := by
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      exact holderProduct_norm_bound _ _
    _ ≤ 2 * ‖increment‖ * (2 * ‖increment‖ * (2 * ‖increment‖ *
          (2 * bound * (2 * bound * (2 * bound * bound))))) := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
