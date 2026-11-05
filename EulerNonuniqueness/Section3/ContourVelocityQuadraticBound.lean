import EulerNonuniqueness.Section3.ContourVelocityCubicTaylor
import EulerNonuniqueness.Section3.ContourTangentInnerLinearBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourVelocityValueQuadraticBound (innerRadius outerRadius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    (8 * contourCauchyParameterOperatorConstant outerRadius * (outerRadius + 2) /
        (outerRadius - innerRadius) + 2 * contourCauchyParameterOperatorConstant outerRadius)

def contourVelocityTangentQuadraticBound (innerRadius outerRadius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    (2 * (outerRadius + 2) * contourTangentInnerQuadraticBound innerRadius outerRadius +
      2 * contourTangentInnerLinearBound outerRadius)

def contourVelocityQuadraticBound (innerRadius outerRadius : ℝ) : ℝ :=
  max (contourVelocityValueQuadraticBound innerRadius outerRadius)
    (contourVelocityTangentQuadraticBound innerRadius outerRadius)

theorem contourVelocityPrefactor_norm : ‖(1 / (4 * Real.pi) : ℂ)‖ = 1 / (4 * Real.pi) := by
  rw [norm_div, norm_one, norm_mul]
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem contourVelocityHolderQuadratic_uniform_norm_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourVelocityHolderQuadratic data increment‖ ≤
      contourVelocityValueQuadraticBound innerRadius outerRadius * ‖increment‖ ^ 2 := by
  have outer_nonnegative := nonnegative.trans gap.le
  have outer_near := nearby.trans_lt gap
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg outer_nonnegative small
  have density_bound : ‖holderConjugate (c1ValueHolder data)‖ ≤ 2 * (outerRadius + 2) :=
    (holderConjugate_norm_bound (c1ValueHolder data)).trans
      ((c1ValueHolder_norm_bound data).trans
        (mul_le_mul_of_nonneg_left
          (PeriodicC1HolderHalf.norm_le_radius_add_two data outer_near.le) (by norm_num)))
  have density_increment : ‖holderConjugate (c1ValueHolder increment)‖ ≤ 2 * ‖increment‖ :=
    (holderConjugate_norm_bound (c1ValueHolder increment)).trans (c1ValueHolder_norm_bound increment)
  have middle_near : ‖data - standardCircleBanach‖ < (innerRadius + outerRadius) / 2 := by linarith
  have middle_gap : (innerRadius + outerRadius) / 2 < outerRadius := by linarith
  have middle_nonnegative : 0 ≤ outerRadius - (innerRadius + outerRadius) / 2 := by linarith
  have second_bound := contourCauchySecondVariation_norm_bound data increment increment
    (holderConjugate (c1ValueHolder data)) middle_near middle_gap small
  have half_bound : ‖(1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
      (holderConjugate (c1ValueHolder data))‖ ≤
      (8 * contourCauchyParameterOperatorConstant outerRadius * (outerRadius + 2) /
        (outerRadius - innerRadius)) * ‖increment‖ ^ 2 := by
    calc
      _ ≤ ‖contourCauchySecondVariation data increment increment
          (holderConjugate (c1ValueHolder data))‖ := by
        rw [norm_smul (1 / 2 : ℂ)
          (contourCauchySecondVariation data increment increment (holderConjugate (c1ValueHolder data)))]
        norm_num only [norm_div, norm_one, Complex.norm_ofNat]
        nlinarith [norm_nonneg (contourCauchySecondVariation data increment increment
          (holderConjugate (c1ValueHolder data)))]
      _ ≤ (2 * contourCauchyParameterOperatorConstant outerRadius * (2 * (outerRadius + 2)) /
          (outerRadius - (innerRadius + outerRadius) / 2)) * ‖increment‖ * ‖increment‖ := by
        apply second_bound.trans
        gcongr
      _ = _ := by field_simp; ring
  have mixed_bound : ‖contourCauchyDirectionalDerivative data increment
      (holderConjugate (c1ValueHolder increment))‖ ≤
      (2 * contourCauchyParameterOperatorConstant outerRadius) * ‖increment‖ ^ 2 := by
    apply (contourCauchyDirectionalDerivative_norm_bound data increment _ outer_near small).trans
    calc
      _ ≤ (contourCauchyParameterOperatorConstant outerRadius * (2 * ‖increment‖)) * ‖increment‖ := by gcongr
      _ = _ := by ring
  unfold contourVelocityHolderQuadratic
  rw [norm_smul (-(1 / (4 * Real.pi) : ℂ))
    (holderConjugate ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
      (holderConjugate (c1ValueHolder data)) +
      contourCauchyDirectionalDerivative data increment (holderConjugate (c1ValueHolder increment)))),
    norm_neg, contourVelocityPrefactor_norm]
  exact (mul_le_mul_of_nonneg_left
    ((holderConjugate_norm_bound _).trans (norm_add_le_of_le half_bound mixed_bound))
    (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))).trans_eq
      (by unfold contourVelocityValueQuadraticBound; ring)

theorem contourVelocityTangentQuadratic_uniform_norm_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourVelocityTangentQuadratic data increment‖ ≤
      contourVelocityTangentQuadraticBound innerRadius outerRadius * ‖increment‖ ^ 2 := by
  have outer_nonnegative := nonnegative.trans gap.le
  have quadratic_bound := (holderConjugate_norm_bound (contourTangentInnerQuadratic data increment)).trans
    (contourTangentInnerQuadratic_uniform_norm_bound data increment nonnegative gap small nearby)
  have linear_bound := (holderConjugate_norm_bound (contourTangentInnerLinear data increment)).trans
    (contourTangentInnerLinear_uniform_norm_bound data increment outer_nonnegative small (nearby.trans_lt gap))
  have tangent_bound := (holderConjugate_norm_bound data.val.2).trans
    ((PeriodicC1HolderHalf.tangent_norm_bound data).trans
      (PeriodicC1HolderHalf.norm_le_radius_add_two data (nearby.trans gap.le)))
  have increment_bound := (holderConjugate_norm_bound increment.val.2).trans
    (PeriodicC1HolderHalf.tangent_norm_bound increment)
  have quadratic_nonnegative := (norm_nonneg _).trans quadratic_bound
  have linear_nonnegative := (norm_nonneg _).trans linear_bound
  unfold contourVelocityTangentQuadratic
  rw [norm_smul (-(1 / (4 * Real.pi) : ℂ))
    (holderProduct (holderConjugate data.val.2) (holderConjugate (contourTangentInnerQuadratic data increment)) +
      holderProduct (holderConjugate increment.val.2) (holderConjugate (contourTangentInnerLinear data increment))),
    norm_neg, contourVelocityPrefactor_norm]
  apply (mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _)))
    (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))).trans
  calc
    _ ≤ (1 / (4 * Real.pi)) *
        (2 * (outerRadius + 2) * (contourTangentInnerQuadraticBound innerRadius outerRadius * ‖increment‖ ^ 2) +
          2 * ‖increment‖ * (contourTangentInnerLinearBound outerRadius * ‖increment‖)) := by gcongr
    _ = _ := by unfold contourVelocityTangentQuadraticBound; ring

theorem contourVelocityQuadratic_uniform_norm_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourVelocityQuadratic data increment ((nearby.trans_lt gap).trans small)‖ ≤
      contourVelocityQuadraticBound innerRadius outerRadius * ‖increment‖ ^ 2 := by
  have value_bound := contourVelocityHolderQuadratic_uniform_norm_bound data increment nonnegative gap small nearby
  have tangent_bound := contourVelocityTangentQuadratic_uniform_norm_bound data increment nonnegative gap small nearby
  have projection : ‖(contourVelocityHolderQuadratic data increment).val.1‖ ≤
      ‖contourVelocityHolderQuadratic data increment‖ :=
    norm_fst_le (contourVelocityHolderQuadratic data increment).val
  change max ‖(contourVelocityHolderQuadratic data increment).val.1‖
    ‖contourVelocityTangentQuadratic data increment‖ ≤ _
  exact max_le
    ((projection.trans value_bound).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
    (tangent_bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))

end

end EulerNonuniqueness.Paper
