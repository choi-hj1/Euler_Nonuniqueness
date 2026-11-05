import EulerNonuniqueness.General.QuadraticExponentialProfileIntegral
import EulerNonuniqueness.General.WeightedExponentialProfileBootstrap

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem weighted_paired_saddle_remainder_le_of_profiles
    {shape state remainder additive : ℝ → ℝ}
    {finish origin rate omega shapeMagnitude stateMagnitude seed endpoint referenceSize constant : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (omegaNonnegative : 0 ≤ omega) (omegaRate : omega ≤ rate)
    (shapeMagnitudeNonnegative : 0 ≤ shapeMagnitude)
    (stateMagnitudeNonnegative : 0 ≤ stateMagnitude) (seedPositive : 0 < seed)
    (referenceNonnegative : 0 ≤ referenceSize) (constantNonnegative : 0 ≤ constant)
    (shapeContinuous : ContinuousOn shape (Icc 0 finish))
    (stateContinuous : ContinuousOn state (Icc 0 finish))
    (remainderContinuous : ContinuousOn remainder (Icc 0 finish))
    (additiveContinuous : ContinuousOn additive (Icc 0 finish))
    (shapeNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ shape time)
    (stateNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ state time)
    (shapeProfile : ∀ time ∈ Icc 0 finish,
      shape time ≤ shapeMagnitude * seed * Real.exp (rate * (time - origin)))
    (stateProfile : ∀ time ∈ Icc 0 finish,
      state time ≤ stateMagnitude * seed * Real.exp (rate * (time - origin)))
    (remainderBound : ∀ time ∈ Icc 0 finish,
      remainder time ≤ constant * omega *
        ((shape time + state time + referenceSize) * shape time + referenceSize * state time) + additive time)
    (exposure : seed * Real.exp (rate * (finish - origin)) ≤ endpoint) :
    Real.exp (rate * origin) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * remainder time) ≤
      constant * (shapeMagnitude * (shapeMagnitude + stateMagnitude) * endpoint +
        omega * referenceSize * (shapeMagnitude + stateMagnitude) * finish) * seed +
      Real.exp (rate * origin) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * additive time) := by
  let quadratic := fun time => shape time * (shape time + state time)
  let linear := fun time => shape time + state time
  let weight := fun time : ℝ => Real.exp (-rate * time)
  have weightContinuous : ContinuousOn weight (Icc 0 finish) := by dsimp only [weight]; fun_prop
  have quadraticI : IntervalIntegrable (fun time => weight time * quadratic time) volume 0 finish :=
    (weightContinuous.mul (shapeContinuous.mul (shapeContinuous.add stateContinuous))).intervalIntegrable_of_Icc finishNonnegative
  have linearI : IntervalIntegrable (fun time => weight time * linear time) volume 0 finish :=
    (weightContinuous.mul (shapeContinuous.add stateContinuous)).intervalIntegrable_of_Icc finishNonnegative
  have remainderI : IntervalIntegrable (fun time => weight time * remainder time) volume 0 finish :=
    (weightContinuous.mul remainderContinuous).intervalIntegrable_of_Icc finishNonnegative
  have additiveI : IntervalIntegrable (fun time => weight time * additive time) volume 0 finish :=
    (weightContinuous.mul additiveContinuous).intervalIntegrable_of_Icc finishNonnegative
  have upperI := ((quadraticI.const_mul (constant * omega)).add
    (linearI.const_mul (constant * omega * referenceSize))).add additiveI
  have comparison := intervalIntegral.integral_mono_on finishNonnegative remainderI upperI
    (by
      intro time inside
      have actual := mul_le_mul_of_nonneg_left (remainderBound time inside) (Real.exp_pos (-rate * time)).le
      convert actual using 1
      dsimp only [quadratic, linear, weight]
      ring)
  rw [intervalIntegral.integral_add ((quadraticI.const_mul _).add (linearI.const_mul _)) additiveI,
    intervalIntegral.integral_add (quadraticI.const_mul _) (linearI.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at comparison
  have quadraticBound := weighted_quadratic_profile_integral_le_of_exposure finishNonnegative ratePositive
    omegaNonnegative omegaRate shapeMagnitudeNonnegative stateMagnitudeNonnegative seedPositive quadraticI
    shapeNonnegative stateNonnegative shapeProfile stateProfile exposure
  have linearProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      linear time ≤ ((shapeMagnitude + stateMagnitude) * seed) * Real.exp (rate * (time - origin)) := by
    have actual := add_le_add (shapeProfile time inside) (stateProfile time inside)
    convert actual using 1
    dsimp only [linear]
    ring
  have linearBound := intervalIntegral.integral_exp_neg_mul_le_of_same_rate_majorant finishNonnegative linearI linearProfile
  have cancellation : Real.exp (rate * origin) * Real.exp (-rate * origin) = 1 := by
    rw [← Real.exp_add, show rate * origin + -rate * origin = 0 by ring, Real.exp_zero]
  have normalizedLinear : Real.exp (rate * origin) *
      (∫ time in (0 : ℝ)..finish, weight time * linear time) ≤
        finish * (shapeMagnitude + stateMagnitude) * seed := by
    have normalized := mul_le_mul_of_nonneg_left linearBound (Real.exp_pos (rate * origin)).le
    apply normalized.trans_eq
    calc
      _ = (finish * (shapeMagnitude + stateMagnitude) * seed) *
          (Real.exp (rate * origin) * Real.exp (-rate * origin)) := by ring
      _ = _ := by rw [cancellation, mul_one]
  have normalizedComparison := mul_le_mul_of_nonneg_left comparison (Real.exp_pos (rate * origin)).le
  have firstTerm := mul_le_mul_of_nonneg_left quadraticBound constantNonnegative
  have secondTerm := mul_le_mul_of_nonneg_left normalizedLinear
    (mul_nonneg (mul_nonneg constantNonnegative omegaNonnegative) referenceNonnegative)
  have combined := add_le_add_right (add_le_add firstTerm secondTerm)
    (Real.exp (rate * origin) * (∫ time in (0 : ℝ)..finish, weight time * additive time))
  apply normalizedComparison.trans
  convert combined using 1 <;> dsimp only [quadratic, weight] <;> ring

end EulerNonuniqueness.General
