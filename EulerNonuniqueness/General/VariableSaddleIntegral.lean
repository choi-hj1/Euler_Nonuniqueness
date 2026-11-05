import EulerNonuniqueness.General.VariableStableBounds

open MeasureTheory Set

namespace EulerNonuniqueness

theorem variable_saddle_integral_bound
    {rate unstable stable unstableForcing stableForcing : ℝ → ℝ}
    {decay horizon terminal forcingBound feedback time : ℝ}
    (decayPositive : 0 < decay)
    (rateContinuous : Continuous rate)
    (unstableContinuous : ContinuousOn unstable (Icc 0 horizon))
    (stableContinuous : ContinuousOn stable (Icc 0 horizon))
    (unstableForcingContinuous : ContinuousOn unstableForcing (Icc 0 horizon))
    (stableForcingContinuous : ContinuousOn stableForcing (Icc 0 horizon))
    (rateLower : ∀ current ∈ Icc 0 horizon, decay ≤ rate current)
    (unstableEquation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt unstable (rate current * unstable current + unstableForcing current) current)
    (stableEquation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt stable (-rate current * stable current + stableForcing current) current)
    (stableInitial : stable 0 = 0) (terminalBound : |unstable horizon| ≤ terminal)
    (forcingNonnegative : 0 ≤ forcingBound) (feedbackNonnegative : 0 ≤ feedback)
    (forcingEstimate : ∀ current ∈ Icc 0 horizon,
      |unstableForcing current| + |stableForcing current| ≤
        forcingBound + feedback * (|unstable current| + |stable current|))
    (inside : time ∈ Icc 0 horizon) :
    |unstable time| + |stable time| ≤
      terminal * Real.exp (-decay * (horizon - time)) + 2 * forcingBound / decay +
        feedback * ∫ current in (0 : ℝ)..horizon,
          Real.exp (-decay * |time - current|) * (|unstable current| + |stable current|) := by
  let envelope := fun current => forcingBound + feedback * (|unstable current| + |stable current|)
  let kernel := fun current => Real.exp (-decay * |time - current|)
  have envelopeContinuous : ContinuousOn envelope (Icc 0 horizon) := by
    exact continuous_const.continuousOn.add
      (continuous_const.continuousOn.mul (unstableContinuous.abs.add stableContinuous.abs))
  have kernelContinuous : Continuous kernel := by dsimp only [kernel]; fun_prop
  have firstSubset : Icc 0 time ⊆ Icc 0 horizon :=
    fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩
  have secondSubset : Icc time horizon ⊆ Icc 0 horizon :=
    fun _ membership => ⟨inside.1.trans membership.1, membership.2⟩
  have unstableBound := scalar_variable_backward_bound rateContinuous unstableForcingContinuous
    rateLower unstableEquation inside
  have stableBound := scalar_variable_forward_bound rateContinuous.neg stableForcingContinuous
    (fun current membership => neg_le_neg (rateLower current membership)) stableEquation inside
  simp only [stableInitial, abs_zero, mul_zero, zero_add] at stableBound
  have firstIntegral : (∫ current in (0 : ℝ)..time,
      Real.exp (-decay * (time - current)) * |stableForcing current|) ≤
      ∫ current in (0 : ℝ)..time, kernel current * envelope current := by
    have leftContinuous : ContinuousOn (fun current => Real.exp (-decay * (time - current)) *
        |stableForcing current|) (Icc 0 time) :=
      (by fun_prop : Continuous (fun current : ℝ => Real.exp (-decay * (time - current)))).continuousOn.mul
        (stableForcingContinuous.mono firstSubset).abs
    apply intervalIntegral.integral_mono_on inside.1
      (leftContinuous.intervalIntegrable_of_Icc inside.1)
      ((kernelContinuous.continuousOn.mul (envelopeContinuous.mono firstSubset)).intervalIntegrable_of_Icc inside.1)
    intro current membership
    have forcingEstimate' := forcingEstimate current (firstSubset membership)
    have kernelIdentity : kernel current = Real.exp (-decay * (time - current)) := by
      dsimp only [kernel]
      rw [abs_of_nonneg (sub_nonneg.mpr membership.2)]
    rw [kernelIdentity]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    dsimp only [envelope]
    linarith [abs_nonneg (unstableForcing current)]
  have secondIntegral : (∫ current in time..horizon,
      Real.exp (-decay * (current - time)) * |unstableForcing current|) ≤
      ∫ current in time..horizon, kernel current * envelope current := by
    have leftContinuous : ContinuousOn (fun current => Real.exp (-decay * (current - time)) *
        |unstableForcing current|) (Icc time horizon) :=
      (by fun_prop : Continuous (fun current : ℝ => Real.exp (-decay * (current - time)))).continuousOn.mul
        (unstableForcingContinuous.mono secondSubset).abs
    apply intervalIntegral.integral_mono_on inside.2
      (leftContinuous.intervalIntegrable_of_Icc inside.2)
      ((kernelContinuous.continuousOn.mul (envelopeContinuous.mono secondSubset)).intervalIntegrable_of_Icc inside.2)
    intro current membership
    have forcingEstimate' := forcingEstimate current (secondSubset membership)
    have kernelIdentity : kernel current = Real.exp (-decay * (current - time)) := by
      dsimp only [kernel]
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr membership.1)]
    rw [kernelIdentity]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    dsimp only [envelope]
    linarith [abs_nonneg (stableForcing current)]
  have joined := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((kernelContinuous.continuousOn.mul (envelopeContinuous.mono firstSubset)).intervalIntegrable_of_Icc inside.1)
    ((kernelContinuous.continuousOn.mul (envelopeContinuous.mono secondSubset)).intervalIntegrable_of_Icc inside.2)
  have preliminary : |unstable time| + |stable time| ≤
      terminal * Real.exp (-decay * (horizon - time)) +
        ∫ current in (0 : ℝ)..horizon, kernel current * envelope current := by
    have terminalEstimate := mul_le_mul_of_nonneg_left terminalBound (Real.exp_pos (-decay * (horizon - time))).le
    linarith
  have integralIdentity : (∫ current in (0 : ℝ)..horizon, kernel current * envelope current) =
      forcingBound * (∫ current in (0 : ℝ)..horizon, kernel current) +
        feedback * ∫ current in (0 : ℝ)..horizon,
          kernel current * (|unstable current| + |stable current|) := by
    have pointwise : (fun current => kernel current * envelope current) =
        fun current => forcingBound * kernel current + feedback *
          (kernel current * (|unstable current| + |stable current|)) := by
      funext current
      dsimp only [envelope]
      ring
    have sourceIntegrable : IntervalIntegrable
        (fun current => kernel current * (|unstable current| + |stable current|)) volume 0 horizon :=
      (kernelContinuous.continuousOn.mul (unstableContinuous.abs.add stableContinuous.abs)).intervalIntegrable_of_Icc
        (inside.1.trans inside.2)
    rw [pointwise, intervalIntegral.integral_add
      ((kernelContinuous.intervalIntegrable 0 horizon).const_mul forcingBound)
      (sourceIntegrable.const_mul feedback)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integralIdentity] at preliminary
  have kernelEstimate := mul_le_mul_of_nonneg_left
    (integral_twoSided_decay_le decayPositive inside) forcingNonnegative
  have constantIdentity : forcingBound * (2 / decay) = 2 * forcingBound / decay := by ring
  rw [constantIdentity] at kernelEstimate
  dsimp only [kernel] at preliminary
  linarith

end EulerNonuniqueness
