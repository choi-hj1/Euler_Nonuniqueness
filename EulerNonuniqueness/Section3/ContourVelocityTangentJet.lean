import EulerNonuniqueness.Section3.ContourTangentInnerCubicBound
import EulerNonuniqueness.Section3.ContourVelocityTangentDerivative
import EulerNonuniqueness.Section3.HolderProductQuadraticJet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourVelocityTangentLinear (data increment : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) •
    (holderProduct (holderConjugate data.val.2) (holderConjugate (contourTangentInnerLinear data increment)) +
      holderProduct (holderConjugate increment.val.2) (holderConjugate (contourTangentInner data)))

def contourVelocityTangentQuadratic (data increment : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) •
    (holderProduct (holderConjugate data.val.2) (holderConjugate (contourTangentInnerQuadratic data increment)) +
      holderProduct (holderConjugate increment.val.2) (holderConjugate (contourTangentInnerLinear data increment)))

theorem contourVelocityTangent_remainder_identity (data increment : PeriodicC1HolderHalf) :
    holderContourVelocityTangent (data + increment) - holderContourVelocityTangent data -
        contourVelocityTangentLinear data increment - contourVelocityTangentQuadratic data increment =
      -(1 / (4 * Real.pi) : ℂ) •
        (holderProduct (holderConjugate (data + increment).val.2)
            (holderConjugate (contourTangentInner (data + increment) - contourTangentInner data -
              contourTangentInnerLinear data increment - contourTangentInnerQuadratic data increment)) +
          holderProduct (holderConjugate increment.val.2)
            (holderConjugate (contourTangentInnerQuadratic data increment))) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change -(1 / (4 * Real.pi) : ℂ) *
      (star (data.val.2.val.1 label + increment.val.2.val.1 label) *
        star (contourTangentInner (data + increment)).val.1 label) -
      (-(1 / (4 * Real.pi) : ℂ) *
        (star (data.val.2.val.1 label) * star (contourTangentInner data).val.1 label)) -
      (-(1 / (4 * Real.pi) : ℂ) *
        (star (data.val.2.val.1 label) * star (contourTangentInnerLinear data increment).val.1 label +
          star (increment.val.2.val.1 label) * star (contourTangentInner data).val.1 label)) -
      (-(1 / (4 * Real.pi) : ℂ) *
        (star (data.val.2.val.1 label) * star (contourTangentInnerQuadratic data increment).val.1 label +
          star (increment.val.2.val.1 label) * star (contourTangentInnerLinear data increment).val.1 label)) =
    -(1 / (4 * Real.pi) : ℂ) *
      (star (data.val.2.val.1 label + increment.val.2.val.1 label) *
          star ((contourTangentInner (data + increment)).val.1 label -
            (contourTangentInner data).val.1 label -
            (contourTangentInnerLinear data increment).val.1 label -
            (contourTangentInnerQuadratic data increment).val.1 label) +
        star (increment.val.2.val.1 label) * star (contourTangentInnerQuadratic data increment).val.1 label)
  simp only [Prod.fst_star, BoundedContinuousFunction.star_apply, Pi.star_apply, star_add, star_sub]
  ring

theorem contourVelocityTangent_cubic_uniform_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (increment_small : ‖increment‖ ≤ (outerRadius - innerRadius) / 4)
    (inverse_small : ‖increment‖ ≤ (1 - outerRadius) / 2) (increment_bound : ‖increment‖ ≤ 1) :
    ‖holderContourVelocityTangent (data + increment) - holderContourVelocityTangent data -
      contourVelocityTangentLinear data increment - contourVelocityTangentQuadratic data increment‖ ≤
      (1 / (4 * Real.pi)) *
        (2 * (outerRadius + 2) * contourTangentInnerCubicBound innerRadius outerRadius +
          2 * contourTangentInnerQuadraticBound innerRadius outerRadius) * ‖increment‖ ^ 3 := by
  have outer_nonnegative := nonnegative.trans gap.le
  have remainder_bound := contourTangentInner_cubic_uniform_bound data increment nonnegative gap small
    nearby increment_small inverse_small increment_bound
  have quadratic_bound := contourTangentInnerQuadratic_uniform_norm_bound data increment nonnegative gap small nearby
  have next_nearby : ‖data + increment - standardCircleBanach‖ ≤ outerRadius := by
    have identity : data + increment - standardCircleBanach =
        (data - standardCircleBanach) + increment := by abel
    rw [identity]
    exact (norm_add_le (data - standardCircleBanach) increment).trans (by linarith)
  have tangent_bound := (holderConjugate_norm_bound (data + increment).val.2).trans
    ((PeriodicC1HolderHalf.tangent_norm_bound (data + increment)).trans
      (PeriodicC1HolderHalf.norm_le_radius_add_two (data + increment) next_nearby))
  have tangent_increment := (holderConjugate_norm_bound increment.val.2).trans
    (PeriodicC1HolderHalf.tangent_norm_bound increment)
  have conjugate_remainder := (holderConjugate_norm_bound
    (contourTangentInner (data + increment) - contourTangentInner data -
      contourTangentInnerLinear data increment - contourTangentInnerQuadratic data increment)).trans remainder_bound
  have conjugate_quadratic :=
    (holderConjugate_norm_bound (contourTangentInnerQuadratic data increment)).trans quadratic_bound
  have remainder_nonnegative := (norm_nonneg _).trans conjugate_remainder
  have quadratic_nonnegative := (norm_nonneg _).trans conjugate_quadratic
  rw [contourVelocityTangent_remainder_identity,
    norm_smul (-(1 / (4 * Real.pi) : ℂ))
      (holderProduct (holderConjugate (data + increment).val.2)
        (holderConjugate (contourTangentInner (data + increment) - contourTangentInner data -
          contourTangentInnerLinear data increment - contourTangentInnerQuadratic data increment)) +
        holderProduct (holderConjugate increment.val.2)
          (holderConjugate (contourTangentInnerQuadratic data increment))), norm_neg]
  have scalar_norm : ‖(1 / (4 * Real.pi) : ℂ)‖ = 1 / (4 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [scalar_norm]
  apply (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans
      (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _)))
    (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))).trans
  calc
    _ ≤ (1 / (4 * Real.pi)) *
        (2 * (outerRadius + 2) * (contourTangentInnerCubicBound innerRadius outerRadius * ‖increment‖ ^ 3) +
          2 * ‖increment‖ * (contourTangentInnerQuadraticBound innerRadius outerRadius * ‖increment‖ ^ 2)) := by
      gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
