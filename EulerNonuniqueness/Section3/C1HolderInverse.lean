import EulerNonuniqueness.Section3.C1HolderBanachAlgebra
import Mathlib.Analysis.Calculus.Deriv.Star

namespace EulerNonuniqueness.Paper

noncomputable section

local instance c1InverseHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance c1InverseNormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def c1InverseTangent (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : PeriodicHolderHalf :=
  holderComplexMul (-1) (holderProduct data.val.2
    (holderProduct (holderInverse (c1ValueHolder data) lower_pos separated)
      (holderInverse (c1ValueHolder data) lower_pos separated)))

theorem c1InverseTangent_value (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (label : ℝ) :
    (c1InverseTangent data lower_pos separated).val.1 label =
      -data.val.2.val.1 label / (data.val.1 label)^2 := by
  simp only [c1InverseTangent, holderComplexMul_value, holderProduct_value,
    holderInverse_value, c1ValueHolder_value]
  simp only [div_eq_mul_inv, inv_pow, pow_two]
  ring

def c1Inverse (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : PeriodicC1HolderHalf := by
  have nonzero : ∀ label, data.val.1 label ≠ 0 := fun label =>
    norm_pos_iff.mp (lower_pos.trans_le (separated label))
  exact PeriodicC1HolderHalf.ofFunctions
    (fun label => (data.val.1 label)⁻¹) (c1InverseTangent data lower_pos separated).val.1
    (data.val.1.continuous.inv₀ nonzero)
    (c1InverseTangent data lower_pos separated).val.1.continuous
    (1 / lower) ‖c1InverseTangent data lower_pos separated‖ ‖c1InverseTangent data lower_pos separated‖
    (fun label => by
      rw [norm_inv]
      exact (inv_anti₀ lower_pos (separated label)).trans_eq (one_div lower).symm)
    (PeriodicHolderHalf.value_bound _) (PeriodicHolderHalf.holder_bound _)
    (fun label => by
      rw [c1InverseTangent_value]
      have derivative := (hasDerivAt_inv (nonzero label)).scomp label
        (PeriodicC1HolderHalf.hasDerivAt data label)
      convert derivative using 1 <;> simp [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm])
    (fun label => by
      dsimp only
      rw [PeriodicC1HolderHalf.periodic data label])
    (PeriodicHolderHalf.periodic _)

theorem c1Inverse_value (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) (label : ℝ) :
    (c1Inverse data lower_pos separated).val.1 label = (data.val.1 label)⁻¹ := rfl

theorem c1Inverse_norm_bound (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    ‖c1Inverse data lower_pos separated‖ ≤
      max (1 / lower) ‖c1InverseTangent data lower_pos separated‖ := by
  have tangent_eq : (c1Inverse data lower_pos separated).val.2 =
      c1InverseTangent data lower_pos separated := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  change max ‖(c1Inverse data lower_pos separated).val.1‖
    ‖(c1Inverse data lower_pos separated).val.2‖ ≤ _
  rw [tangent_eq]
  apply max_le_max _ le_rfl
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro label
  rw [c1Inverse_value, norm_inv]
  exact (inv_anti₀ lower_pos (separated label)).trans_eq (one_div lower).symm

theorem c1InverseTangent_norm_bound (data : PeriodicC1HolderHalf) {lower : ℝ} (lower_pos : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) :
    ‖c1InverseTangent data lower_pos separated‖ ≤
      4 * ‖data‖ * (max (1 / lower) (2 * ‖data‖ / lower^2))^2 := by
  let inverse := holderInverse (c1ValueHolder data) lower_pos separated
  have inverse_bound : ‖inverse‖ ≤ max (1 / lower) (2 * ‖data‖ / lower^2) :=
    (holderInverse_norm_bound (c1ValueHolder data) lower_pos separated).trans
      (max_le_max le_rfl (div_le_div_of_nonneg_right (c1ValueHolder_norm_bound data) (sq_nonneg lower)))
  have tangent_bound : ‖data.val.2‖ ≤ ‖data‖ := le_max_right _ _
  have square_bound : ‖holderProduct inverse inverse‖ ≤
      2 * (max (1 / lower) (2 * ‖data‖ / lower^2))^2 := by
    have product_bound := holderProduct_norm_bound inverse inverse
    have inverse_nonneg : 0 ≤ max (1 / lower) (2 * ‖data‖ / lower^2) := by positivity
    have squares := mul_self_le_mul_self (norm_nonneg inverse) inverse_bound
    nlinarith
  have main_bound := holderProduct_norm_bound data.val.2 (holderProduct inverse inverse)
  have product_bound := mul_le_mul tangent_bound square_bound (norm_nonneg _) (norm_nonneg data)
  have scalar_bound := holderComplexMul_norm_bound (-1) (holderProduct data.val.2 (holderProduct inverse inverse))
  change ‖holderComplexMul (-1) (holderProduct data.val.2 (holderProduct inverse inverse))‖ ≤ _
  norm_num only [norm_neg, norm_one, one_mul] at scalar_bound
  nlinarith

theorem c1Inverse_difference_identity (first second : PeriodicC1HolderHalf)
    {firstLower secondLower : ℝ} (first_pos : 0 < firstLower) (second_pos : 0 < secondLower)
    (first_separated : ∀ label, firstLower ≤ ‖first.val.1 label‖)
    (second_separated : ∀ label, secondLower ≤ ‖second.val.1 label‖) :
    c1Inverse first first_pos first_separated - c1Inverse second second_pos second_separated =
      c1Product (c1Product (c1Inverse first first_pos first_separated)
        (c1Inverse second second_pos second_separated)) (second - first) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (c1Inverse first first_pos first_separated).val.1 label -
    (c1Inverse second second_pos second_separated).val.1 label = _
  rw [c1Product_value, c1Product_value, c1Inverse_value, c1Inverse_value]
  change (first.val.1 label)⁻¹ - (second.val.1 label)⁻¹ =
    (first.val.1 label)⁻¹ * (second.val.1 label)⁻¹ * (second.val.1 label - first.val.1 label)
  have first_ne := norm_pos_iff.mp (first_pos.trans_le (first_separated label))
  have second_ne := norm_pos_iff.mp (second_pos.trans_le (second_separated label))
  field_simp

theorem c1Inverse_difference_norm_bound (first second : PeriodicC1HolderHalf)
    {firstLower secondLower : ℝ} (first_pos : 0 < firstLower) (second_pos : 0 < secondLower)
    (first_separated : ∀ label, firstLower ≤ ‖first.val.1 label‖)
    (second_separated : ∀ label, secondLower ≤ ‖second.val.1 label‖) :
    ‖c1Inverse first first_pos first_separated - c1Inverse second second_pos second_separated‖ ≤
      64 * ‖c1Inverse first first_pos first_separated‖ *
        ‖c1Inverse second second_pos second_separated‖ * ‖first - second‖ := by
  rw [c1Inverse_difference_identity]
  apply (c1Product_norm_bound _ _).trans
  have product := c1Product_norm_bound (c1Inverse first first_pos first_separated)
    (c1Inverse second second_pos second_separated)
  have multiplied := mul_le_mul_of_nonneg_right product (norm_nonneg (second - first))
  rw [norm_sub_rev second first] at multiplied ⊢
  nlinarith

end

end EulerNonuniqueness.Paper
