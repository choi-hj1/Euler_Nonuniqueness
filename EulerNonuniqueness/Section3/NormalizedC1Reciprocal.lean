import EulerNonuniqueness.Section3.C1InverseUniform

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

def normalizedC1DenominatorLinear (parameter : ℂ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  -c1ProductCLM (c1Constant parameter)

def normalizedC1Denominator (parameter : ℂ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Constant 1 + normalizedC1DenominatorLinear parameter data

def normalizedC1Reciprocal (parameter : ℂ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  extendedC1Inverse (normalizedC1Denominator parameter data)

def normalizedC1ReciprocalDerivative (parameter : ℂ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (fderiv ℝ extendedC1Inverse (normalizedC1Denominator parameter data)).comp
    (normalizedC1DenominatorLinear parameter)

theorem normalizedC1DenominatorLinear_norm_le (parameter : ℂ) :
    ‖normalizedC1DenominatorLinear parameter‖ ≤ 8 * ‖parameter‖ := by
  rw [normalizedC1DenominatorLinear, norm_neg]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro data
  exact (c1Product_norm_bound (c1Constant parameter) data).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (c1Constant_norm_bound parameter) (by norm_num))
      (norm_nonneg data))

theorem normalizedC1Denominator_hasFDerivAt (parameter : ℂ) (data : PeriodicC1HolderHalf) :
    HasFDerivAt (normalizedC1Denominator parameter) (normalizedC1DenominatorLinear parameter) data := by
  exact (normalizedC1DenominatorLinear parameter).hasFDerivAt.const_add (c1Constant 1)

theorem normalizedC1Denominator_difference_norm_le (parameter : ℂ) (first final : PeriodicC1HolderHalf) :
    ‖normalizedC1Denominator parameter first - normalizedC1Denominator parameter final‖ ≤
      8 * ‖parameter‖ * ‖first - final‖ := by
  have identity : normalizedC1Denominator parameter first - normalizedC1Denominator parameter final =
      normalizedC1DenominatorLinear parameter (first - final) := by
    simp only [normalizedC1Denominator, map_sub]
    abel
  rw [identity]
  exact ((normalizedC1DenominatorLinear parameter).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (normalizedC1DenominatorLinear_norm_le parameter) (norm_nonneg _))

theorem normalizedC1Denominator_value (parameter : ℂ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (normalizedC1Denominator parameter data).val.1 label = 1 - parameter * data.val.1 label := by
  change 1 + -(parameter * data.val.1 label) = 1 - parameter * data.val.1 label
  ring

theorem normalizedC1Reciprocal_value (parameter : ℂ) (data : PeriodicC1HolderHalf)
    (small : ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ 1 / 2) (label : ℝ) :
    (normalizedC1Reciprocal parameter data).val.1 label = (1 - parameter * data.val.1 label)⁻¹ := by
  rw [normalizedC1Reciprocal, extendedC1Inverse_value _ (show (0 : ℝ) < 1 / 2 by norm_num)
    (c1_near_one_separated _ small), normalizedC1Denominator_value]

theorem normalizedC1Reciprocal_exists_uniform_bounds :
    ∃ parameterRadius > 0, ∃ constant ≥ 1, ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius →
      (∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 3 →
        ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ 1 / 2 ∧
        ‖normalizedC1Reciprocal parameter data‖ ≤ 5 / 2 ∧
        ‖normalizedC1Reciprocal parameter data - c1Constant 1‖ ≤ constant * ‖parameter‖ ∧
        HasFDerivAt (normalizedC1Reciprocal parameter) (normalizedC1ReciprocalDerivative parameter data) data ∧
        ‖normalizedC1ReciprocalDerivative parameter data‖ ≤ constant * ‖parameter‖) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 3 → ‖final‖ ≤ 3 →
        ‖normalizedC1Reciprocal parameter first - normalizedC1Reciprocal parameter final‖ ≤
          constant * ‖parameter‖ * ‖first - final‖ ∧
        ‖normalizedC1ReciprocalDerivative parameter first - normalizedC1ReciprocalDerivative parameter final‖ ≤
          constant * ‖parameter‖ ^ 2 * ‖first - final‖ := by
  obtain ⟨radius, positive, radiusHalf, constant, one, actual, valueDifference, derivativeDifference⟩ :=
    extendedC1Inverse_exists_uniform_ball
  have constantPositive : 0 < constant := lt_of_lt_of_le zero_lt_one one
  let parameterRadius := min (radius / 48) (1 / (48 * constant))
  have parameterPositive : 0 < parameterRadius := by dsimp [parameterRadius]; positivity
  have enlargedOne : 1 ≤ 96 * constant := by linarith
  refine ⟨parameterRadius, parameterPositive, 96 * constant, enlargedOne, ?_⟩
  intro parameter parameterSmall
  have radiusSmall : 48 * ‖parameter‖ ≤ radius := by
    have bound := parameterSmall.trans (min_le_left _ _)
    linarith
  have constantSmall : 48 * constant * ‖parameter‖ ≤ 1 := by
    have bound := parameterSmall.trans (min_le_right _ _)
    have actual := (le_div_iff₀ (show (0 : ℝ) < 48 * constant by positivity)).mp bound
    nlinarith
  have operatorBound := normalizedC1DenominatorLinear_norm_le parameter
  have inputBound (data : PeriodicC1HolderHalf) (bounded : ‖data‖ ≤ 3) :
      ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ 24 * ‖parameter‖ := by
    change ‖(c1Constant 1 + normalizedC1DenominatorLinear parameter data) - c1Constant 1‖ ≤ _
    rw [add_sub_cancel_left]
    have applied := ((normalizedC1DenominatorLinear parameter).le_opNorm data).trans
      (mul_le_mul operatorBound bounded (norm_nonneg data) (by positivity))
    exact applied.trans_eq (by ring)
  have inside (data : PeriodicC1HolderHalf) (bounded : ‖data‖ ≤ 3) :
      ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ radius := by
    exact (inputBound data bounded).trans (by nlinarith [norm_nonneg parameter])
  have inverseBound (data : PeriodicC1HolderHalf) (bounded : ‖data‖ ≤ 3) :
      ‖normalizedC1Reciprocal parameter data - c1Constant 1‖ ≤ 24 * constant * ‖parameter‖ := by
    have estimate := valueDifference (normalizedC1Denominator parameter data) (c1Constant 1)
      (inside data bounded) (by simpa only [sub_self, norm_zero] using positive.le)
    rw [extendedC1Inverse_one] at estimate
    exact estimate.trans ((mul_le_mul_of_nonneg_left (inputBound data bounded) constantPositive.le).trans_eq (by ring))
  constructor
  · intro data bounded
    have dataInside := inside data bounded
    have inverseActual := (actual _ dataInside).1.hasFDerivAt
    have inverseDerivativeBound := (actual _ dataInside).2
    have candidate := inverseActual.comp data (normalizedC1Denominator_hasFDerivAt parameter data)
    have derivativeActual : HasFDerivAt (normalizedC1Reciprocal parameter)
        (normalizedC1ReciprocalDerivative parameter data) data := candidate
    have valueBound : ‖normalizedC1Reciprocal parameter data‖ ≤ 5 / 2 := by
      have triangle := norm_add_le (normalizedC1Reciprocal parameter data - c1Constant 1) (c1Constant 1)
      rw [sub_add_cancel] at triangle
      have constantNorm : ‖c1Constant 1‖ ≤ 1 := by simpa only [norm_one] using c1Constant_norm_bound (1 : ℂ)
      have inverseSmall := inverseBound data bounded
      nlinarith
    have derivativeBound : ‖normalizedC1ReciprocalDerivative parameter data‖ ≤ 8 * constant * ‖parameter‖ := by
      have estimate := (fderiv ℝ extendedC1Inverse (normalizedC1Denominator parameter data)).opNorm_comp_le
        (normalizedC1DenominatorLinear parameter)
      exact (estimate.trans (mul_le_mul inverseDerivativeBound operatorBound (norm_nonneg _) constantPositive.le)).trans_eq (by ring)
    refine ⟨dataInside.trans radiusHalf, valueBound, ?_, derivativeActual, ?_⟩
    · exact (inverseBound data bounded).trans (by nlinarith [norm_nonneg parameter])
    · exact derivativeBound.trans (by nlinarith [norm_nonneg parameter])
  · intro first final firstBound finalBound
    have firstInside := inside first firstBound
    have finalInside := inside final finalBound
    have values := valueDifference _ _ firstInside finalInside
    have inputs := normalizedC1Denominator_difference_norm_le parameter first final
    have valueBound := values.trans (mul_le_mul_of_nonneg_left inputs constantPositive.le)
    have derivatives := derivativeDifference _ _ firstInside finalInside
    have derivativeBound := derivatives.trans (mul_le_mul_of_nonneg_left inputs constantPositive.le)
    constructor
    · exact valueBound.trans (by nlinarith [mul_nonneg (norm_nonneg parameter) (norm_nonneg (first - final))])
    · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro direction
      let firstDerivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
        fderiv ℝ extendedC1Inverse (normalizedC1Denominator parameter first)
      let finalDerivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
        fderiv ℝ extendedC1Inverse (normalizedC1Denominator parameter final)
      let next := normalizedC1DenominatorLinear parameter direction
      have applied : ‖firstDerivative next - finalDerivative next‖ ≤
          ‖firstDerivative - finalDerivative‖ * ‖next‖ :=
        (firstDerivative - finalDerivative).le_opNorm next
      have nextBound := ((normalizedC1DenominatorLinear parameter).le_opNorm direction).trans
        (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg direction))
      have estimate := applied.trans (mul_le_mul derivativeBound nextBound (norm_nonneg next) (by positivity))
      change ‖firstDerivative next - finalDerivative next‖ ≤ _
      apply estimate.trans
      have nonnegative : 0 ≤ constant * ‖parameter‖ ^ 2 * ‖first - final‖ * ‖direction‖ := by positivity
      nlinarith only [nonnegative]

end EulerNonuniqueness.Paper
