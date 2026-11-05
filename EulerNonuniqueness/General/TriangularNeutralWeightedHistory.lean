import EulerNonuniqueness.General.InteriorDerivativeIntegralMajorant
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem weighted_norm_of_interior_derivative_majorant
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {curve velocity : ℝ → Space} {majorant : ℝ → ℝ} {horizon weight : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (weightPositive : 0 < weight)
    (curveContinuous : ContinuousOn curve (Icc 0 horizon)) (initial : curve 0 = 0)
    (majorantContinuous : ContinuousOn majorant (Icc 0 horizon))
    (majorantNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ majorant time)
    (equation : ∀ time ∈ Ioo 0 horizon, HasDerivAt curve (velocity time) time)
    (bound : ∀ time ∈ Ioo 0 horizon, ‖velocity time‖ ≤ majorant time) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * ‖curve time‖) ≤
      (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * majorant time) / weight := by
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ‖curve time‖ ≤ ∫ current in (0 : ℝ)..time, majorant current := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl inside.2
    have actual := norm_sub_le_integral_of_interior_derivative_majorant inside.1
      (curveContinuous.mono subset) (majorantContinuous.mono subset)
      (fun current member => majorantNonnegative current (subset member))
      (fun current member => equation current ⟨member.1, member.2.trans_le inside.2⟩)
      (fun current member => bound current ⟨member.1, member.2.trans_le inside.2⟩)
    simpa only [initial, sub_zero] using actual
  have integrable := majorantContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have primitiveContinuous : ContinuousOn (fun time => ∫ current in (0 : ℝ)..time, majorant current) (Icc 0 horizon) := by
    simpa only [uIcc_of_le horizonNonnegative] using
      intervalIntegral.continuousOn_primitive_interval' integrable left_mem_uIcc
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    ((weightContinuous.continuousOn.mul curveContinuous.norm).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative)
    ((weightContinuous.continuousOn.mul primitiveContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative)
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have convolution := EulerNonuniqueness.weighted_exponential_convolution_integral_le
    (rate := (0 : ℝ)) majorantContinuous weightPositive horizonNonnegative majorantNonnegative
  simp only [zero_mul, Real.exp_zero, one_mul, sub_zero] at convolution
  exact comparison.trans convolution

theorem triangular_neutral_weighted_history
    {dilation phase dilationVelocity phaseVelocity source phaseSource : ℝ → ℝ}
    {horizon weight coupling : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (weightPositive : 0 < weight) (couplingNonnegative : 0 ≤ coupling)
    (dilationContinuous : ContinuousOn dilation (Icc 0 horizon)) (dilationInitial : dilation 0 = 0)
    (phaseContinuous : ContinuousOn phase (Icc 0 horizon)) (phaseInitial : phase 0 = 0)
    (sourceContinuous : ContinuousOn source (Icc 0 horizon))
    (phaseSourceContinuous : ContinuousOn phaseSource (Icc 0 horizon))
    (sourceNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ source time)
    (phaseSourceNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ phaseSource time)
    (dilationEquation : ∀ time ∈ Ioo 0 horizon, HasDerivAt dilation (dilationVelocity time) time)
    (phaseEquation : ∀ time ∈ Ioo 0 horizon, HasDerivAt phase (phaseVelocity time) time)
    (dilationBound : ∀ time ∈ Ioo 0 horizon, |dilationVelocity time| ≤ source time)
    (phaseBound : ∀ time ∈ Ioo 0 horizon, |phaseVelocity time| ≤ coupling * |dilation time| + phaseSource time) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * |dilation time|) ≤
        (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * source time) / weight ∧
    (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * |phase time|) ≤
      coupling / weight ^ 2 * (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * source time) +
        (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * phaseSource time) / weight := by
  have first := weighted_norm_of_interior_derivative_majorant horizonNonnegative weightPositive
    dilationContinuous dilationInitial sourceContinuous sourceNonnegative dilationEquation
    (by simpa only [Real.norm_eq_abs] using dilationBound)
  have majorantContinuous : ContinuousOn (fun time => coupling * |dilation time| + phaseSource time) (Icc 0 horizon) :=
    (continuousOn_const.mul dilationContinuous.abs).add phaseSourceContinuous
  have second := weighted_norm_of_interior_derivative_majorant horizonNonnegative weightPositive
    phaseContinuous phaseInitial majorantContinuous
    (fun time inside => add_nonneg (mul_nonneg couplingNonnegative (abs_nonneg _)) (phaseSourceNonnegative time inside))
    phaseEquation (by simpa only [Real.norm_eq_abs] using phaseBound)
  simp only [Real.norm_eq_abs] at first second
  refine ⟨first, ?_⟩
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have firstIntegrable := (weightContinuous.continuousOn.mul dilationContinuous.abs).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have sourceIntegrable := (weightContinuous.continuousOn.mul phaseSourceContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have integralIdentity :
      (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * (coupling * |dilation time| + phaseSource time)) =
        coupling * (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * |dilation time|) +
          ∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * phaseSource time := by
    simp_rw [mul_add, mul_left_comm _ coupling]
    rw [intervalIntegral.integral_add (firstIntegrable.const_mul coupling) sourceIntegrable,
      intervalIntegral.integral_const_mul]
  rw [integralIdentity] at second
  have enlarged := second.trans (div_le_div_of_nonneg_right
    (add_le_add_right (mul_le_mul_of_nonneg_left first couplingNonnegative) _) weightPositive.le)
  have scalarIdentity (firstSource finalSource : ℝ) :
      (coupling * (firstSource / weight) + finalSource) / weight =
        coupling / weight ^ 2 * firstSource + finalSource / weight := by
    field_simp
    <;> ring
  exact enlarged.trans_eq (scalarIdentity _ _)

end EulerNonuniqueness.General
