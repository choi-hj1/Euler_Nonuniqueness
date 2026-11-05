import EulerNonuniqueness.Section3.HolderInverseCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def holderConjugateQuotient (data : PeriodicHolderHalf) : PeriodicHolderHalf :=
  holderProduct (holderConjugate data) (extendedHolderInverse data)

def holderQuotientLinear (data increment : PeriodicHolderHalf) : PeriodicHolderHalf :=
  holderProduct (holderConjugate data) (holderInverseDerivativeCLM data increment) +
    holderProduct (holderConjugate increment) (extendedHolderInverse data)

def holderQuotientQuadratic (data increment : PeriodicHolderHalf) : PeriodicHolderHalf :=
  holderProduct (holderConjugate data) (holderInverseQuadratic data increment) +
    holderProduct (holderConjugate increment) (holderInverseDerivativeCLM data increment)

theorem holderQuotient_cubic_remainder_identity (data increment : PeriodicHolderHalf) :
    holderConjugateQuotient (data + increment) - holderConjugateQuotient data -
        holderQuotientLinear data increment - holderQuotientQuadratic data increment =
      holderProduct (holderConjugate (data + increment))
        (extendedHolderInverse (data + increment) - extendedHolderInverse data -
          holderInverseDerivativeCLM data increment - holderInverseQuadratic data increment) +
      holderProduct (holderConjugate increment) (holderInverseQuadratic data increment) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change star (data.val.1 label + increment.val.1 label) *
      (extendedHolderInverse (data + increment)).val.1 label -
      star (data.val.1 label) * (extendedHolderInverse data).val.1 label -
      (star (data.val.1 label) * (holderInverseDerivativeCLM data increment).val.1 label +
        star (increment.val.1 label) * (extendedHolderInverse data).val.1 label) -
      (star (data.val.1 label) * (holderInverseQuadratic data increment).val.1 label +
        star (increment.val.1 label) * (holderInverseDerivativeCLM data increment).val.1 label) =
    star (data.val.1 label + increment.val.1 label) *
      ((extendedHolderInverse (data + increment)).val.1 label -
        (extendedHolderInverse data).val.1 label -
        (holderInverseDerivativeCLM data increment).val.1 label -
        (holderInverseQuadratic data increment).val.1 label) +
      star (increment.val.1 label) * (holderInverseQuadratic data increment).val.1 label
  rw [star_add]
  ring

theorem holderInverseQuadratic_norm_bound (data increment : PeriodicHolderHalf)
    {bound : ℝ} (bound_nonnegative : 0 ≤ bound)
    (inverse_bound : ‖extendedHolderInverse data‖ ≤ bound) :
    ‖holderInverseQuadratic data increment‖ ≤ (16 * bound ^ 3) * ‖increment‖ ^ 2 := by
  unfold holderInverseQuadratic
  calc
    _ ≤ 2 * ‖increment‖ * (2 * ‖increment‖ *
        (2 * ‖extendedHolderInverse data‖ *
          (2 * ‖extendedHolderInverse data‖ * ‖extendedHolderInverse data‖))) := by
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      exact holderProduct_norm_bound _ _
    _ ≤ 2 * ‖increment‖ * (2 * ‖increment‖ * (2 * bound * (2 * bound * bound))) := by gcongr
    _ = _ := by ring

theorem holderQuotient_cubic_remainder_norm (data increment : PeriodicHolderHalf)
    {lower bound incrementBound : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (small : ‖increment‖ ≤ lower / 2)
    (bound_nonnegative : 0 ≤ bound) (first_bound : ‖extendedHolderInverse data‖ ≤ bound)
    (second_bound : ‖extendedHolderInverse (data + increment)‖ ≤ bound)
    (increment_bound : ‖increment‖ ≤ incrementBound) :
    ‖holderConjugateQuotient (data + increment) - holderConjugateQuotient data -
      holderQuotientLinear data increment - holderQuotientQuadratic data increment‖ ≤
      (128 * (‖data‖ + incrementBound) * bound ^ 4 + 32 * bound ^ 3) * ‖increment‖ ^ 3 := by
  rw [holderQuotient_cubic_remainder_identity]
  have inverse_remainder := holderInverse_cubic_remainder_norm data increment positive separated small
    bound_nonnegative first_bound second_bound
  have quadratic_bound := holderInverseQuadratic_norm_bound data increment bound_nonnegative first_bound
  have incrementBound_nonnegative : 0 ≤ incrementBound := (norm_nonneg increment).trans increment_bound
  have conjugate_bound : ‖holderConjugate (data + increment)‖ ≤ ‖data‖ + incrementBound :=
    (holderConjugate_norm_bound (data + increment)).trans
      ((norm_add_le data increment).trans (add_le_add_left increment_bound _))
  apply (norm_add_le _ _).trans
  apply (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _)).trans
  calc
    _ ≤ 2 * (‖data‖ + incrementBound) * ((64 * bound ^ 4) * ‖increment‖ ^ 3) +
        2 * ‖increment‖ * ((16 * bound ^ 3) * ‖increment‖ ^ 2) := by
      gcongr
      exact holderConjugate_norm_bound increment
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
