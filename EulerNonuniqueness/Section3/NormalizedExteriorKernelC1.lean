import EulerNonuniqueness.Section3.NormalizedC1Reciprocal
import EulerNonuniqueness.Section3.C1PowerFirstJetLipschitz
import EulerNonuniqueness.Section3.ContourInversePowerNormalization

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

def normalizedExteriorKernelC1 (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Conjugate (c1NaturalPower (normalizedC1Reciprocal parameter data) (power + 1)) - c1Constant 1

def normalizedExteriorKernelC1Derivative (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  c1ConjugateCLM.comp ((c1NaturalPowerFirstJet (normalizedC1Reciprocal parameter data) (power + 1)).comp
    (normalizedC1ReciprocalDerivative parameter data))

theorem c1NaturalPower_constant_one (power : ℕ) :
    c1NaturalPower (c1Constant 1) power = c1Constant 1 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [c1NaturalPower_value]
  change (1 : ℂ) ^ power = 1
  exact one_pow _

theorem c1Conjugate_constant_one : c1Conjugate (c1Constant 1) = c1Constant 1 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  exact star_one _

theorem normalizedExteriorKernelC1_value (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf)
    (small : ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ 1 / 2) (label : ℝ) :
    (normalizedExteriorKernelC1 parameter power data).val.1 label =
      normalizedExteriorInversePowerKernel parameter power (data.val.1 label) := by
  change star ((c1NaturalPower (normalizedC1Reciprocal parameter data) (power + 1)).val.1 label) - 1 = _
  rw [c1NaturalPower_value, normalizedC1Reciprocal_value parameter data small label]
  simp only [normalizedExteriorInversePowerKernel, star_pow, star_inv₀]

theorem normalizedExteriorKernelC1_exists_uniform_bounds :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 3 →
        ‖normalizedExteriorKernelC1 parameter power data‖ ≤ constant * (48 : ℝ) ^ (power + 1) * ‖parameter‖ ∧
        HasFDerivAt (normalizedExteriorKernelC1 parameter power)
          (normalizedExteriorKernelC1Derivative parameter power data) data ∧
        ‖normalizedExteriorKernelC1Derivative parameter power data‖ ≤
          constant * (48 : ℝ) ^ (power + 1) * ‖parameter‖ := by
  obtain ⟨parameterRadius, positive, constant, one, bounds⟩ := normalizedC1Reciprocal_exists_uniform_bounds
  refine ⟨parameterRadius, positive, constant, one, ?_⟩
  intro parameter parameterSmall power data dataBound
  have control := (bounds parameter parameterSmall).1 data dataBound
  have oneNorm : ‖c1Constant (1 : ℂ)‖ ≤ 1 := by simpa only [norm_one] using c1Constant_norm_bound (1 : ℂ)
  have powerDifference := c1NaturalPower_difference_geometric_bound
    (normalizedC1Reciprocal parameter data) (c1Constant 1) (by linarith [control.2.1])
    (by linarith) (power + 1)
  rw [c1NaturalPower_constant_one] at powerDifference
  have conjugateDifference := c1Conjugate_difference_norm_bound
    (c1NaturalPower (normalizedC1Reciprocal parameter data) (power + 1)) (c1Constant 1)
  rw [c1Conjugate_constant_one] at conjugateDifference
  have valueBound : ‖normalizedExteriorKernelC1 parameter power data‖ ≤
      constant * (48 : ℝ) ^ (power + 1) * ‖parameter‖ := by
    apply (conjugateDifference.trans powerDifference).trans
    exact (mul_le_mul_of_nonneg_left control.2.2.1 (by positivity)).trans_eq (by ring)
  have actualPower := hasFDerivAt_c1NaturalPowerFirstJet (normalizedC1Reciprocal parameter data)
    (by linarith [control.2.1]) (power + 1)
  have actual := (c1ConjugateCLM.hasFDerivAt.comp data
    (actualPower.comp data control.2.2.2.1)).sub_const (c1Constant 1)
  have derivativeActual : HasFDerivAt (normalizedExteriorKernelC1 parameter power)
      (normalizedExteriorKernelC1Derivative parameter power data) data := by
    simpa only [normalizedExteriorKernelC1, normalizedExteriorKernelC1Derivative,
      ContinuousLinearMap.comp_assoc] using actual
  have derivativeBound : ‖normalizedExteriorKernelC1Derivative parameter power data‖ ≤
      constant * (48 : ℝ) ^ (power + 1) * ‖parameter‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    have conjugate := c1Conjugate_norm_bound
      (c1NaturalPowerFirstJet (normalizedC1Reciprocal parameter data) (power + 1)
        (normalizedC1ReciprocalDerivative parameter data direction))
    have powerBound := c1NaturalPowerFirstJet_apply_geometric_bound
      (normalizedC1Reciprocal parameter data) (normalizedC1ReciprocalDerivative parameter data direction)
      (by linarith [control.2.1]) (power + 1)
    have reciprocalBound := ((normalizedC1ReciprocalDerivative parameter data).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right control.2.2.2.2 (norm_nonneg direction))
    exact ((conjugate.trans powerBound).trans
      (mul_le_mul_of_nonneg_left reciprocalBound (by positivity))).trans_eq (by ring)
  exact ⟨valueBound, derivativeActual, derivativeBound⟩

end EulerNonuniqueness.Paper
