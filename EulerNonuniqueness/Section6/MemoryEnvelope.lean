import EulerNonuniqueness.General.ExponentialVolterra
import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem volterra_two_exponential_bound {trajectory forcing : ℝ → ℝ}
    {initial rate feedback multiplier horizon fastRate slowRate fastAmplitude slowAmplitude : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (initialNonnegative : 0 ≤ initial) (feedbackNonnegative : 0 ≤ feedback)
    (multiplierNonnegative : 0 ≤ multiplier) (horizonNonnegative : 0 ≤ horizon)
    (fastNonnegative : 0 ≤ fastAmplitude) (slowNonnegative : 0 ≤ slowAmplitude)
    (fastRateBound : rate + multiplier * feedback < fastRate)
    (slowRateBound : rate + multiplier * feedback < slowRate)
    (forcingBound : ∀ time ∈ Icc 0 horizon,
      forcing time ≤ fastAmplitude * Real.exp (fastRate * time) + slowAmplitude * Real.exp (slowRate * time))
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (forcing current + feedback * trajectory current)) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤
      multiplier * fastAmplitude / (fastRate - (rate + multiplier * feedback)) * Real.exp (fastRate * time) +
        (initial + multiplier * slowAmplitude / (slowRate - (rate + multiplier * feedback))) * Real.exp (slowRate * time) := by
  have resolved := exponential_volterra_gronwall trajectoryContinuous forcingContinuous feedbackNonnegative
    multiplierNonnegative horizonNonnegative inequality
  intro time inside
  let effectiveRate := rate + multiplier * feedback
  have intervalInside : uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : ContinuousOn (fun current => Real.exp (effectiveRate * (time - current))) (uIcc 0 time) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have fastContinuous : Continuous (fun current : ℝ => fastAmplitude * Real.exp (fastRate * current)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have slowContinuous : Continuous (fun current : ℝ => slowAmplitude * Real.exp (slowRate * current)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have integralBound : (∫ current in (0 : ℝ)..time, Real.exp (effectiveRate * (time - current)) * forcing current) ≤
      (∫ current in (0 : ℝ)..time, Real.exp (effectiveRate * (time - current)) *
        (fastAmplitude * Real.exp (fastRate * current) + slowAmplitude * Real.exp (slowRate * current))) := by
    apply intervalIntegral.integral_mono_on inside.1
      (kernelContinuous.mul (forcingContinuous.mono intervalInside)).intervalIntegrable
      (kernelContinuous.mul (fastContinuous.add slowContinuous).continuousOn).intervalIntegrable
    intro current currentInside
    exact mul_le_mul_of_nonneg_left (forcingBound current ⟨currentInside.1, currentInside.2.trans inside.2⟩) (Real.exp_pos _).le
  have fastIntegrable : IntervalIntegrable (fun current => Real.exp (effectiveRate * (time - current)) *
      (fastAmplitude * Real.exp (fastRate * current))) volume 0 time :=
    (kernelContinuous.mul fastContinuous.continuousOn).intervalIntegrable
  have slowIntegrable : IntervalIntegrable (fun current => Real.exp (effectiveRate * (time - current)) *
      (slowAmplitude * Real.exp (slowRate * current))) volume 0 time :=
    (kernelContinuous.mul slowContinuous.continuousOn).intervalIntegrable
  simp_rw [mul_add] at integralBound
  rw [intervalIntegral.integral_add fastIntegrable slowIntegrable] at integralBound
  have convolutionBound := integralBound.trans (add_le_add
    (exponential_convolution_le fastRateBound fastNonnegative)
    (exponential_convolution_le slowRateBound slowNonnegative))
  have initialBound : initial * Real.exp (effectiveRate * time) ≤ initial * Real.exp (slowRate * time) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right slowRateBound.le inside.1)) initialNonnegative
  have bound := (resolved time inside).trans (add_le_add initialBound
    (mul_le_mul_of_nonneg_left convolutionBound multiplierNonnegative))
  convert bound using 1 <;> dsimp only [effectiveRate] <;> ring

end EulerNonuniqueness.Section6
