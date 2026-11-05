import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem integrating_factor_hasDerivAt {trajectory input : ℝ → ℝ} {rate time : ℝ}
    (equation : HasDerivAt trajectory (rate * trajectory time + input time) time) :
    HasDerivAt (fun currentTime => Real.exp (-rate * currentTime) * trajectory currentTime)
      (Real.exp (-rate * time) * input time) time := by
  convert (((hasDerivAt_id time).const_mul (-rate)).exp).mul equation using 1
  simp only [id_eq, mul_one]
  ring

theorem scalar_duhamel {trajectory input : ℝ → ℝ} {rate horizon time : ℝ}
    (inputContinuous : ContinuousOn input (Icc 0 horizon))
    (equation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt trajectory (rate * trajectory currentTime + input currentTime) currentTime)
    (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    trajectory time = Real.exp (rate * time) *
      (trajectory 0 + ∫ currentTime in (0 : ℝ)..time, Real.exp (-rate * currentTime) * input currentTime) := by
  have intervalInside : Set.uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le timeNonnegative]
    exact Icc_subset_Icc le_rfl timeBound
  have integrable : IntervalIntegrable (fun currentTime => Real.exp (-rate * currentTime) * input currentTime)
      volume 0 time := by
    apply ContinuousOn.intervalIntegrable
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (inputContinuous.mono intervalInside)
  have integralIdentity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun currentTime bounds => integrating_factor_hasDerivAt (equation currentTime (intervalInside bounds))) integrable
  simp only [mul_zero, Real.exp_zero, one_mul] at integralIdentity
  have cancellation : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    trajectory time = Real.exp (rate * time) * (Real.exp (-rate * time) * trajectory time) := by
      rw [← mul_assoc, cancellation, one_mul]
    _ = _ := by rw [integralIdentity]; ring

theorem scalar_duhamel_convolution {trajectory input : ℝ → ℝ} {rate horizon time : ℝ}
    (inputContinuous : ContinuousOn input (Icc 0 horizon))
    (equation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt trajectory (rate * trajectory currentTime + input currentTime) currentTime)
    (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    trajectory time = Real.exp (rate * time) * trajectory 0 +
      ∫ currentTime in (0 : ℝ)..time, Real.exp (rate * (time - currentTime)) * input currentTime := by
  rw [scalar_duhamel inputContinuous equation timeNonnegative timeBound, mul_add,
    ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro currentTime _
  change Real.exp (rate * time) * (Real.exp (-rate * currentTime) * input currentTime) =
    Real.exp (rate * (time - currentTime)) * input currentTime
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

theorem integral_exp_mul_real {rate first last : ℝ} (rateNonzero : rate ≠ 0) :
    (∫ time in first..last, Real.exp (rate * time)) =
      (Real.exp (rate * last) - Real.exp (rate * first)) / rate := by
  have derivative : ∀ time : ℝ, HasDerivAt (fun currentTime => Real.exp (rate * currentTime) / rate)
      (Real.exp (rate * time)) time := by
    intro time
    convert (((hasDerivAt_id time).const_mul rate).exp).div_const rate using 1
    simp only [id_eq, mul_one]
    field_simp
  have integrable : IntervalIntegrable (fun time => Real.exp (rate * time)) volume first last :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time) integrable]
  ring

theorem exponential_convolution {growth decay amplitude time : ℝ} (differentRates : decay < growth) :
    (∫ currentTime in (0 : ℝ)..time,
      Real.exp (decay * (time - currentTime)) * (amplitude * Real.exp (growth * currentTime))) =
      amplitude * (Real.exp (growth * time) - Real.exp (decay * time)) / (growth - decay) := by
  have integrandIdentity : (fun currentTime : ℝ =>
      Real.exp (decay * (time - currentTime)) * (amplitude * Real.exp (growth * currentTime))) =
      (fun currentTime => (amplitude * Real.exp (decay * time)) * Real.exp ((growth - decay) * currentTime)) := by
    funext currentTime
    calc
      _ = amplitude * (Real.exp (decay * (time - currentTime)) * Real.exp (growth * currentTime)) := by ring
      _ = _ := by rw [mul_assoc amplitude, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  rw [integrandIdentity, intervalIntegral.integral_const_mul, integral_exp_mul_real (sub_pos.mpr differentRates).ne']
  simp only [mul_zero, Real.exp_zero]
  have product : Real.exp (decay * time) * Real.exp ((growth - decay) * time) = Real.exp (growth * time) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = amplitude * (Real.exp (decay * time) * Real.exp ((growth - decay) * time) -
      Real.exp (decay * time)) / (growth - decay) := by ring
    _ = _ := by rw [product]

theorem exponential_convolution_le {growth decay amplitude time : ℝ}
    (differentRates : decay < growth) (amplitudeNonnegative : 0 ≤ amplitude) :
    (∫ currentTime in (0 : ℝ)..time,
      Real.exp (decay * (time - currentTime)) * (amplitude * Real.exp (growth * currentTime))) ≤
      amplitude * Real.exp (growth * time) / (growth - decay) := by
  rw [exponential_convolution differentRates]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) amplitudeNonnegative)
    (sub_pos.mpr differentRates).le

theorem weighted_duhamel_error {trajectory input majorant : ℝ → ℝ}
    {rate horizon time error : ℝ}
    (inputContinuous : ContinuousOn input (Icc 0 horizon))
    (majorantContinuous : ContinuousOn majorant (Icc 0 horizon))
    (equation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt trajectory (rate * trajectory currentTime + input currentTime) currentTime)
    (inputBound : ∀ currentTime ∈ Icc 0 horizon,
      |input currentTime| ≤ Real.exp (rate * currentTime) * (error + majorant currentTime))
    (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    |Real.exp (-rate * time) * trajectory time - trajectory 0| ≤
      error * time + ∫ currentTime in (0 : ℝ)..time, majorant currentTime := by
  have intervalInside : Set.uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le timeNonnegative]
    exact Icc_subset_Icc le_rfl timeBound
  have expCancellation (currentTime : ℝ) :
      Real.exp (-rate * currentTime) * Real.exp (rate * currentTime) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have identity : Real.exp (-rate * time) * trajectory time - trajectory 0 =
      ∫ currentTime in (0 : ℝ)..time, Real.exp (-rate * currentTime) * input currentTime := by
    rw [scalar_duhamel inputContinuous equation timeNonnegative timeBound,
      ← mul_assoc, expCancellation, one_mul]
    ring
  have weightedContinuous : ContinuousOn
      (fun currentTime => Real.exp (-rate * currentTime) * input currentTime) (uIcc 0 time) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (inputContinuous.mono intervalInside)
  have boundContinuous : ContinuousOn (fun currentTime => error + majorant currentTime)
      (uIcc 0 time) := continuousOn_const.add (majorantContinuous.mono intervalInside)
  rw [identity]
  calc
    _ ≤ ∫ currentTime in (0 : ℝ)..time, |Real.exp (-rate * currentTime) * input currentTime| :=
      intervalIntegral.abs_integral_le_integral_abs timeNonnegative
    _ ≤ ∫ currentTime in (0 : ℝ)..time, error + majorant currentTime := by
      apply intervalIntegral.integral_mono_on timeNonnegative
        weightedContinuous.abs.intervalIntegrable boundContinuous.intervalIntegrable
      intro currentTime bounds
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (-rate * currentTime) *
            (Real.exp (rate * currentTime) * (error + majorant currentTime)) :=
          mul_le_mul_of_nonneg_left (inputBound currentTime
            ⟨bounds.1, bounds.2.trans timeBound⟩) (Real.exp_pos _).le
        _ = _ := by rw [← mul_assoc, expCancellation, one_mul]
    _ = _ := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (majorantContinuous.mono intervalInside).intervalIntegrable]
      simp [mul_comm]

theorem positive_return_envelope {trajectory kernel : ℝ → ℝ}
    {rate time amplitude multiplier smallness : ℝ}
    (timeNonnegative : 0 ≤ time) (amplitudeNonnegative : 0 ≤ amplitude)
    (multiplierNonnegative : 0 ≤ multiplier)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 time))
    (kernelContinuous : ContinuousOn kernel (Icc 0 time))
    (kernelNonnegative : ∀ currentTime ∈ Icc 0 time, 0 ≤ kernel currentTime)
    (trajectoryBound : ∀ currentTime ∈ Icc 0 time,
      trajectory currentTime ≤ amplitude * Real.exp (rate * currentTime))
    (weightedKernelBound : multiplier + ∫ currentTime in (0 : ℝ)..time,
      kernel currentTime * Real.exp (rate * (currentTime - time)) ≤ smallness) :
    multiplier * trajectory time + ∫ currentTime in (0 : ℝ)..time,
      kernel currentTime * trajectory currentTime ≤
      smallness * amplitude * Real.exp (rate * time) := by
  have expIdentity (currentTime : ℝ) :
      Real.exp (rate * time) * Real.exp (rate * (currentTime - time)) =
        Real.exp (rate * currentTime) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have envelopeContinuous : ContinuousOn
      (fun currentTime => amplitude * Real.exp (rate * currentTime)) (Icc 0 time) :=
    continuousOn_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have integralBound : (∫ currentTime in (0 : ℝ)..time,
      kernel currentTime * trajectory currentTime) ≤
      ∫ currentTime in (0 : ℝ)..time,
        kernel currentTime * (amplitude * Real.exp (rate * currentTime)) := by
    apply intervalIntegral.integral_mono_on timeNonnegative
      ((kernelContinuous.mul trajectoryContinuous).intervalIntegrable_of_Icc timeNonnegative)
      ((kernelContinuous.mul envelopeContinuous).intervalIntegrable_of_Icc timeNonnegative)
    intro currentTime bounds
    exact mul_le_mul_of_nonneg_left (trajectoryBound currentTime bounds)
      (kernelNonnegative currentTime bounds)
  have integralIdentity : (∫ currentTime in (0 : ℝ)..time,
      kernel currentTime * (amplitude * Real.exp (rate * currentTime))) =
      (amplitude * Real.exp (rate * time)) * ∫ currentTime in (0 : ℝ)..time,
        kernel currentTime * Real.exp (rate * (currentTime - time)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro currentTime _
    change kernel currentTime * (amplitude * Real.exp (rate * currentTime)) =
      (amplitude * Real.exp (rate * time)) *
        (kernel currentTime * Real.exp (rate * (currentTime - time)))
    rw [← expIdentity currentTime]
    ring
  calc
    _ ≤ multiplier * (amplitude * Real.exp (rate * time)) +
        ∫ currentTime in (0 : ℝ)..time,
          kernel currentTime * (amplitude * Real.exp (rate * currentTime)) :=
      add_le_add (mul_le_mul_of_nonneg_left (trajectoryBound time ⟨timeNonnegative, le_rfl⟩)
        multiplierNonnegative) integralBound
    _ = (amplitude * Real.exp (rate * time)) *
        (multiplier + ∫ currentTime in (0 : ℝ)..time,
          kernel currentTime * Real.exp (rate * (currentTime - time))) := by
      rw [integralIdentity]
      ring
    _ ≤ _ := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left weightedKernelBound
          (mul_nonneg amplitudeNonnegative (Real.exp_pos _).le)

theorem duhamel_perturbation_bound {trajectory reference forcing remainder majorant : ℝ → ℝ}
    {rate horizon time error : ℝ}
    (remainderContinuous : ContinuousOn remainder (Icc 0 horizon))
    (majorantContinuous : ContinuousOn majorant (Icc 0 horizon))
    (trajectoryEquation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt trajectory
        (rate * trajectory currentTime + forcing currentTime + remainder currentTime) currentTime)
    (referenceEquation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt reference (rate * reference currentTime + forcing currentTime) currentTime)
    (sameInitialData : trajectory 0 = reference 0)
    (remainderBound : ∀ currentTime ∈ Icc 0 horizon,
      |remainder currentTime| ≤ Real.exp (rate * currentTime) * (error + majorant currentTime))
    (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    |Real.exp (-rate * time) * (trajectory time - reference time)| ≤
      error * time + ∫ currentTime in (0 : ℝ)..time, majorant currentTime := by
  have differenceEquation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt (fun currentTime => trajectory currentTime - reference currentTime)
        (rate * (trajectory currentTime - reference currentTime) + remainder currentTime) currentTime := by
    intro currentTime bounds
    convert (trajectoryEquation currentTime bounds).sub (referenceEquation currentTime bounds) using 1; ring
  have bound := weighted_duhamel_error remainderContinuous majorantContinuous
    differenceEquation remainderBound timeNonnegative timeBound
  simpa only [sameInitialData, sub_self, sub_zero] using bound

theorem exponential_exit_time {rate amplitude threshold time : ℝ}
    (ratePositive : 0 < rate) (amplitudePositive : 0 < amplitude)
    (exitIdentity : amplitude * Real.exp (rate * time) = threshold) :
    time = Real.log (threshold / amplitude) / rate := by
  have expIdentity : Real.exp (rate * time) = threshold / amplitude := by
    apply (eq_div_iff amplitudePositive.ne').mpr
    simpa [mul_comm] using exitIdentity
  have logarithmicIdentity := congrArg Real.log expIdentity
  rw [Real.log_exp] at logarithmicIdentity
  exact (eq_div_iff ratePositive.ne').mpr (by nlinarith)

theorem neutral_jordan_duhamel {first second firstInput secondInput : ℝ → ℝ}
    {horizon time : ℝ}
    (firstInputContinuous : ContinuousOn firstInput (Icc 0 horizon))
    (secondInputContinuous : ContinuousOn secondInput (Icc 0 horizon))
    (firstEquation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt first (firstInput currentTime) currentTime)
    (secondEquation : ∀ currentTime ∈ Icc 0 horizon,
      HasDerivAt second (first currentTime + secondInput currentTime) currentTime)
    (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon) :
    second time = second 0 + time * first 0 + ∫ currentTime in (0 : ℝ)..time,
      ((time - currentTime) * firstInput currentTime + secondInput currentTime) := by
  have intervalInside : Set.uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le timeNonnegative]
    exact Icc_subset_Icc le_rfl timeBound
  have derivative : ∀ currentTime ∈ uIcc 0 time,
      HasDerivAt (fun currentTime => (time - currentTime) * first currentTime + second currentTime)
        ((time - currentTime) * firstInput currentTime + secondInput currentTime) currentTime := by
    intro currentTime bounds
    convert (((hasDerivAt_const currentTime time).sub (hasDerivAt_id currentTime)).mul
      (firstEquation currentTime (intervalInside bounds))).add
        (secondEquation currentTime (intervalInside bounds)) using 1 <;> simp <;> ring
  have integrable : IntervalIntegrable (fun currentTime =>
      (time - currentTime) * firstInput currentTime + secondInput currentTime) volume 0 time := by
    exact (((continuous_const.sub continuous_id).continuousOn.mul
      (firstInputContinuous.mono intervalInside)).add
        (secondInputContinuous.mono intervalInside)).intervalIntegrable
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable
  simp only [sub_self, zero_mul, zero_add, sub_zero] at identity
  linarith

end EulerNonuniqueness.Section6
