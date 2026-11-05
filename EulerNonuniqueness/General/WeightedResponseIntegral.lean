import Mathlib

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem weighted_response_integral_le {response forcing : ℝ → ℝ} {rate weight horizon : ℝ}
    (responseContinuous : Continuous response) (forcingContinuous : Continuous forcing)
    (equation : ∀ time, HasDerivAt response (rate * response time + forcing time) time)
    (initial : response 0 = 0) (nonnegative : 0 ≤ response horizon)
    (rateBound : rate < weight) (horizonNonnegative : 0 ≤ horizon) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * response time) ≤
      (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * forcing time) / (weight - rate) := by
  have responseIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * response time) volume 0 horizon :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul responseContinuous).intervalIntegrable _ _
  have forcingIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 horizon :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul forcingContinuous).intervalIntegrable _ _
  have derivative (time : ℝ) : HasDerivAt (fun current => Real.exp (-weight * current) * response current)
      ((rate - weight) * (Real.exp (-weight * time) * response time) + Real.exp (-weight * time) * forcing time) time := by
    convert (((hasDerivAt_id time).const_mul (-weight)).exp).mul (equation time) using 1
    simp only [id_eq, mul_one]
    ring
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    ((responseIntegrable.const_mul (rate - weight)).add forcingIntegrable)
  rw [intervalIntegral.integral_add (responseIntegrable.const_mul _) forcingIntegrable,
    intervalIntegral.integral_const_mul, initial, mul_zero, sub_zero] at identity
  apply (le_div_iff₀ (sub_pos.mpr rateBound)).mpr
  have endpointNonnegative : 0 ≤ Real.exp (-weight * horizon) * response horizon :=
    mul_nonneg (Real.exp_pos _).le nonnegative
  nlinarith

def exponentialResponse (rate : ℝ) (forcing : ℝ → ℝ) (time : ℝ) : ℝ :=
  Real.exp (rate * time) * ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current

theorem exponentialResponse_eq_integral (rate : ℝ) (forcing : ℝ → ℝ) (time : ℝ) :
    exponentialResponse rate forcing time =
      ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current := by
  rw [exponentialResponse, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro current _
  change Real.exp (rate * time) * (Real.exp (-rate * current) * forcing current) = _
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem hasDerivAt_exponentialResponse {forcing : ℝ → ℝ} (continuous : Continuous forcing)
    (rate time : ℝ) : HasDerivAt (exponentialResponse rate forcing)
      (rate * exponentialResponse rate forcing time + forcing time) time := by
  have weightedContinuous : Continuous (fun current => Real.exp (-rate * current) * forcing current) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous
  have primitiveDerivative := intervalIntegral.integral_hasDerivAt_right
    (weightedContinuous.intervalIntegrable 0 time)
    weightedContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter weightedContinuous.continuousAt
  have cancellation : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  convert (((hasDerivAt_id time).const_mul rate).exp).mul primitiveDerivative using 1
  dsimp only [exponentialResponse, id_eq]
  rw [mul_one, ← mul_assoc (Real.exp (rate * time)), cancellation, one_mul]
  ring

theorem exponentialResponse_nonnegative {forcing : ℝ → ℝ} {rate time : ℝ}
    (timeNonnegative : 0 ≤ time) (forcingNonnegative : ∀ current ∈ Icc 0 time, 0 ≤ forcing current) :
    0 ≤ exponentialResponse rate forcing time := by
  apply mul_nonneg (Real.exp_pos _).le
  exact intervalIntegral.integral_nonneg timeNonnegative fun current inside =>
    mul_nonneg (Real.exp_pos _).le (forcingNonnegative current inside)

theorem weighted_exponentialResponse_integral_le {forcing : ℝ → ℝ} {rate weight horizon : ℝ}
    (continuous : Continuous forcing) (rateBound : rate < weight) (horizonNonnegative : 0 ≤ horizon)
    (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * exponentialResponse rate forcing time) ≤
      (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * forcing time) / (weight - rate) := by
  exact weighted_response_integral_le
    (continuous_iff_continuousAt.mpr fun time => (hasDerivAt_exponentialResponse continuous rate time).continuousAt)
    continuous (hasDerivAt_exponentialResponse continuous rate)
    (by simp [exponentialResponse]) (exponentialResponse_nonnegative horizonNonnegative nonnegative)
    rateBound horizonNonnegative

theorem weighted_exponential_convolution_integral_le {forcing : ℝ → ℝ} {rate weight horizon : ℝ}
    (continuous : ContinuousOn forcing (Icc 0 horizon)) (rateBound : rate < weight)
    (horizonNonnegative : 0 ≤ horizon) (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) *
      (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current)) ≤
      (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * forcing time) / (weight - rate) := by
  let extended := fun time : ℝ => forcing (projIcc 0 horizon horizonNonnegative time)
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp continuous).comp continuous_projIcc
  have equal (time : ℝ) (inside : time ∈ Icc 0 horizon) : extended time = forcing time := by
    simp only [extended, projIcc_of_mem horizonNonnegative inside]
  have extendedNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ extended time := by
    intro time inside
    rw [equal time inside]
    exact nonnegative time inside
  have estimate := weighted_exponentialResponse_integral_le extendedContinuous rateBound
    horizonNonnegative extendedNonnegative
  have responseEqual (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      exponentialResponse rate extended time =
        ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current := by
    rw [exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current currentInside
    rw [uIcc_of_le inside.1] at currentInside
    change Real.exp (rate * (time - current)) * extended current = _
    rw [equal current ⟨currentInside.1, currentInside.2.trans inside.2⟩]
  have leftEquality : (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * exponentialResponse rate extended time) =
      ∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) *
        (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current) := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le horizonNonnegative] at inside
    change Real.exp (-weight * time) * exponentialResponse rate extended time = _
    rw [responseEqual time inside]
  have rightEquality : (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * extended time) =
      ∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * forcing time := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le horizonNonnegative] at inside
    change Real.exp (-weight * time) * extended time = _
    rw [equal time inside]
  rwa [leftEquality, rightEquality] at estimate

end EulerNonuniqueness
