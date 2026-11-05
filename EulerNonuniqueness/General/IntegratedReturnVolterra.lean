import EulerNonuniqueness.General.IntegratedExponentialVolterra
import EulerNonuniqueness.General.ExponentialMajorant
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.General

theorem integrated_return_volterra_on_Icc
    {trajectory forcing coefficient : ℝ → ℝ} {multiplier feedback growth decay horizon : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (coefficientContinuous : ContinuousOn coefficient (Icc 0 horizon))
    (horizonNonnegative : 0 ≤ horizon) (multiplierNonnegative : 0 ≤ multiplier)
    (feedbackNonnegative : 0 ≤ feedback) (gap : decay < growth)
    (trajectoryNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ trajectory time)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (coefficientNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ coefficient time)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤
      multiplier * ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) *
        (forcing current + coefficient current * trajectory current +
          feedback * ∫ earlier in (0 : ℝ)..current, Real.exp (decay * (current - earlier)) * trajectory earlier))
    (small : 2 * Real.exp (multiplier * ∫ current in (0 : ℝ)..horizon, coefficient current) *
      multiplier * feedback * horizon ≤ growth - decay) :
    ∀ time ∈ Icc 0 horizon, Real.exp (-growth * time) * trajectory time ≤
      2 * Real.exp (multiplier * ∫ current in (0 : ℝ)..horizon, coefficient current) * multiplier *
        ∫ current in (0 : ℝ)..horizon, Real.exp (-growth * current) * forcing current := by
  let kernel := fun time => ∫ current in (0 : ℝ)..time, Real.exp (decay * (time - current)) * trajectory current
  let extended := fun time => trajectory (projIcc 0 horizon horizonNonnegative time)
  have extendedContinuous : Continuous extended :=
    continuousOn_iff_continuous_restrict.mp trajectoryContinuous |>.comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 horizon) : extended time = trajectory time := by
    simp only [extended, projIcc_of_mem horizonNonnegative inside]
  have kernelAgreement (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      EulerNonuniqueness.exponentialResponse decay extended time = kernel time := by
    rw [EulerNonuniqueness.exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    change Real.exp (decay * (time - current)) * extended current = _
    rw [agreement current ⟨member.1, member.2.trans inside.2⟩]
  have responseContinuous : Continuous (EulerNonuniqueness.exponentialResponse decay extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (EulerNonuniqueness.hasDerivAt_exponentialResponse extendedContinuous decay time).continuousAt
  have kernelContinuous : ContinuousOn kernel (Icc 0 horizon) :=
    responseContinuous.continuousOn.congr (fun time inside => (kernelAgreement time inside).symm)
  have kernelNonnegative (time : ℝ) (inside : time ∈ Icc 0 horizon) : 0 ≤ kernel time :=
    intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
      (trajectoryNonnegative current ⟨member.1, member.2.trans inside.2⟩))
  have prefixIntegral (function : ℝ → ℝ) (regular : ContinuousOn function (Icc 0 horizon))
      (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ function time) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      (∫ current in (0 : ℝ)..time, function current) ≤ ∫ current in (0 : ℝ)..horizon, function current := by
    apply intervalIntegral.integral_mono_interval le_rfl inside.1 inside.2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with current member
      exact nonnegative current ⟨member.1.le, member.2⟩
    · exact regular.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have weightedTrajectoryContinuous := exponentialContinuous.continuousOn.mul trajectoryContinuous
  have weightedForcingContinuous := exponentialContinuous.continuousOn.mul forcingContinuous
  have weightedKernelContinuous := exponentialContinuous.continuousOn.mul kernelContinuous
  have augmentedContinuous : ContinuousOn (fun time => forcing time + feedback * kernel time) (Icc 0 horizon) :=
    forcingContinuous.add (continuousOn_const.mul kernelContinuous)
  have augmentedNonnegative (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      0 ≤ forcing time + feedback * kernel time :=
    add_nonneg (forcingNonnegative time inside) (mul_nonneg feedbackNonnegative (kernelNonnegative time inside))
  have gronwall := exponential_volterra_of_integrated_coefficient_on_Icc trajectoryContinuous augmentedContinuous coefficientContinuous
    horizonNonnegative multiplierNonnegative augmentedNonnegative coefficientNonnegative
    (initial := 0) (rate := growth) (by
      intro time inside
      simpa only [zero_mul, zero_add, kernel, add_assoc, add_left_comm, add_comm] using inequality time inside)
  simp only [zero_add] at gronwall
  let cost := Real.exp (multiplier * ∫ current in (0 : ℝ)..horizon, coefficient current)
  let forcingMass := ∫ current in (0 : ℝ)..horizon, Real.exp (-growth * current) * forcing current
  let trajectoryMass := ∫ current in (0 : ℝ)..horizon, Real.exp (-growth * current) * trajectory current
  let kernelMass := ∫ current in (0 : ℝ)..horizon, Real.exp (-growth * current) * kernel current
  have costPositive : 0 < cost := Real.exp_pos _
  have forcingIntegrable := weightedForcingContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have trajectoryIntegrable := weightedTrajectoryContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have kernelIntegrable := weightedKernelContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have fullIntegral : (∫ current in (0 : ℝ)..horizon, Real.exp (-growth * current) *
      (forcing current + feedback * kernel current)) = forcingMass + feedback * kernelMass := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) feedback]
    rw [intervalIntegral.integral_add forcingIntegrable (kernelIntegrable.const_mul feedback), intervalIntegral.integral_const_mul]
  have uniformBound (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      Real.exp (-growth * time) * trajectory time ≤ cost * multiplier * (forcingMass + feedback * kernelMass) := by
    have coefficientPrefix := prefixIntegral coefficient coefficientContinuous coefficientNonnegative time inside
    have exponentialBound : Real.exp (multiplier * ∫ current in (0 : ℝ)..time, coefficient current) ≤ cost :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left coefficientPrefix multiplierNonnegative)
    have integralPrefix := prefixIntegral (fun current => Real.exp (-growth * current) *
      (forcing current + feedback * kernel current)) (exponentialContinuous.continuousOn.mul augmentedContinuous)
      (fun current member => mul_nonneg (Real.exp_pos _).le (augmentedNonnegative current member)) time inside
    have prefixNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) *
        (forcing current + feedback * kernel current) :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
        (augmentedNonnegative current ⟨member.1, member.2.trans inside.2⟩))
    have first := mul_le_mul_of_nonneg_right exponentialBound (mul_nonneg multiplierNonnegative prefixNonnegative)
    have second := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left integralPrefix multiplierNonnegative) costPositive.le
    have actual := (gronwall time inside).trans (first.trans second)
    rw [fullIntegral] at actual
    simpa only [zero_add, mul_assoc] using actual
  obtain ⟨bound, boundNonnegative, majorant, maximumTime, maximumInside, attained⟩ :=
    EulerNonuniqueness.exists_attained_exponential_majorant (rate := growth) horizonNonnegative trajectoryContinuous trajectoryNonnegative
  have cancellation (time : ℝ) : Real.exp (-growth * time) * Real.exp (growth * time) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have weightedMajorant (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      Real.exp (-growth * time) * trajectory time ≤ bound := by
    have actual := mul_le_mul_of_nonneg_left (majorant time inside) (Real.exp_pos (-growth * time)).le
    calc
      _ ≤ Real.exp (-growth * time) * (bound * Real.exp (growth * time)) := actual
      _ = bound := by rw [mul_left_comm, cancellation, mul_one]
  have attainedWeighted : Real.exp (-growth * maximumTime) * trajectory maximumTime = bound := by
    rw [attained, mul_left_comm, cancellation, mul_one]
  have massBound : trajectoryMass ≤ bound * horizon := by
    have actual := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative trajectoryIntegrable
      (continuous_const.intervalIntegrable (μ := volume) 0 horizon) weightedMajorant
    simpa only [trajectoryMass, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using actual
  have convolution := EulerNonuniqueness.weighted_exponential_convolution_integral_le
    trajectoryContinuous gap horizonNonnegative trajectoryNonnegative
  change kernelMass ≤ trajectoryMass / (growth - decay) at convolution
  have kernelBound : kernelMass ≤ bound * horizon / (growth - decay) :=
    convolution.trans (div_le_div_of_nonneg_right massBound (sub_pos.mpr gap).le)
  have attainedBound := uniformBound maximumTime maximumInside
  rw [attainedWeighted] at attainedBound
  have feedbackBound := mul_le_mul_of_nonneg_left kernelBound feedbackNonnegative
  have normalized : bound ≤ cost * multiplier * forcingMass +
      (cost * multiplier * feedback * horizon / (growth - decay)) * bound := by
    have actual := attainedBound.trans (mul_le_mul_of_nonneg_left (add_le_add_left feedbackBound forcingMass)
      (mul_nonneg costPositive.le multiplierNonnegative))
    exact actual.trans_eq (by ring)
  have halfCoefficient : cost * multiplier * feedback * horizon / (growth - decay) ≤ 1 / 2 := by
    apply (div_le_iff₀ (sub_pos.mpr gap)).mpr
    change 2 * cost * multiplier * feedback * horizon ≤ growth - decay at small
    linarith only [small]
  have halfBound := mul_le_mul_of_nonneg_right halfCoefficient boundNonnegative
  have absorbed : bound ≤ 2 * cost * multiplier * forcingMass := by
    linarith only [normalized, halfBound]
  intro time inside
  exact (weightedMajorant time inside).trans absorbed

end EulerNonuniqueness.General
