import EulerNonuniqueness.Section3.NormalizedExteriorKernelC1

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

theorem normalizedExteriorKernelC1_exists_uniform_derivative_difference :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 3 → ‖final‖ ≤ 3 →
        ‖normalizedExteriorKernelC1Derivative parameter power first -
          normalizedExteriorKernelC1Derivative parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 * ‖first - final‖ := by
  obtain ⟨parameterRadius, positive, constant, one, bounds⟩ := normalizedC1Reciprocal_exists_uniform_bounds
  refine ⟨parameterRadius, positive, constant + 8 * constant ^ 2, by nlinarith [sq_nonneg constant], ?_⟩
  intro parameter parameterSmall power first final firstBound finalBound
  have firstControl := (bounds parameter parameterSmall).1 first firstBound
  have finalControl := (bounds parameter parameterSmall).1 final finalBound
  have pairControl := (bounds parameter parameterSmall).2 first final firstBound finalBound
  let firstPower := c1NaturalPowerFirstJet (normalizedC1Reciprocal parameter first) (power + 1)
  let finalPower := c1NaturalPowerFirstJet (normalizedC1Reciprocal parameter final) (power + 1)
  let firstReciprocal := normalizedC1ReciprocalDerivative parameter first
  let finalReciprocal := normalizedC1ReciprocalDerivative parameter final
  have powers : (48 : ℝ) ^ (power + 1) ≤ (96 : ℝ) ^ (power + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have firstPowerBound : ‖firstPower‖ ≤ (96 : ℝ) ^ (power + 1) :=
    (c1NaturalPowerFirstJet_norm_bound _ (by linarith [firstControl.2.1]) _).trans powers
  have powerDifference : ‖firstPower - finalPower‖ ≤
      8 * (96 : ℝ) ^ (power + 1) * (constant * ‖parameter‖ * ‖first - final‖) :=
    (c1NaturalPowerFirstJet_difference_geometric_bound _ _ firstControl.2.1 finalControl.2.1 _).trans
      (mul_le_mul_of_nonneg_left pairControl.1 (by positivity))
  have identity : firstPower.comp firstReciprocal - finalPower.comp finalReciprocal =
      firstPower.comp (firstReciprocal - finalReciprocal) +
        (firstPower - finalPower).comp finalReciprocal := by
    apply ContinuousLinearMap.ext
    intro direction
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, map_sub]
    abel
  have product : ‖firstPower.comp firstReciprocal - finalPower.comp finalReciprocal‖ ≤
      ‖firstPower‖ * ‖firstReciprocal - finalReciprocal‖ +
        ‖firstPower - finalPower‖ * ‖finalReciprocal‖ := by
    rw [identity]
    exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
      (ContinuousLinearMap.opNorm_comp_le _ _))
  have estimated : ‖firstPower.comp firstReciprocal - finalPower.comp finalReciprocal‖ ≤
      (96 : ℝ) ^ (power + 1) * (constant * ‖parameter‖ ^ 2 * ‖first - final‖) +
        (8 * (96 : ℝ) ^ (power + 1) * (constant * ‖parameter‖ * ‖first - final‖)) *
          (constant * ‖parameter‖) :=
    product.trans (add_le_add
      (mul_le_mul firstPowerBound pairControl.2 (norm_nonneg _) (by positivity))
      (mul_le_mul powerDifference finalControl.2.2.2.2 (norm_nonneg _) (by positivity)))
  have conjugateBound : ‖c1ConjugateCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro direction
    simpa only [one_mul] using c1Conjugate_norm_bound direction
  have actualIdentity : normalizedExteriorKernelC1Derivative parameter power first -
      normalizedExteriorKernelC1Derivative parameter power final =
      c1ConjugateCLM.comp (firstPower.comp firstReciprocal - finalPower.comp finalReciprocal) := by
    apply ContinuousLinearMap.ext
    intro direction
    change c1ConjugateCLM (firstPower (firstReciprocal direction)) -
        c1ConjugateCLM (finalPower (finalReciprocal direction)) =
      c1ConjugateCLM (firstPower (firstReciprocal direction) - finalPower (finalReciprocal direction))
    exact (c1ConjugateCLM.map_sub _ _).symm
  rw [actualIdentity]
  have actual : ‖c1ConjugateCLM.comp (firstPower.comp firstReciprocal - finalPower.comp finalReciprocal)‖ ≤
      ‖firstPower.comp firstReciprocal - finalPower.comp finalReciprocal‖ := by
    exact ((c1ConjugateCLM.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_right conjugateBound (norm_nonneg
        (firstPower.comp firstReciprocal - finalPower.comp finalReciprocal)))).trans_eq (one_mul _)
  exact (actual.trans estimated).trans_eq (by ring)

end EulerNonuniqueness.Paper
