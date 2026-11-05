import EulerNonuniqueness.General.VariableSaddleIntegral
import EulerNonuniqueness.General.TwoSidedTubeEstimate

open MeasureTheory Set

namespace EulerNonuniqueness.Section5

theorem reference_interior_tube_of_actual_equations
    {rate unstable stable unstableForcing stableForcing : ℝ → ℝ}
    {decay horizon radius forcingBound quadratic : ℝ}
    (decayPositive : 0 < decay) (horizonNonnegative : 0 ≤ horizon)
    (radiusPositive : 0 < radius) (forcingNonnegative : 0 ≤ forcingBound)
    (quadraticNonnegative : 0 ≤ quadratic)
    (small : 16 * quadratic * radius ≤ decay)
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
    (stableInitial : stable 0 = 0)
    (bootstrap : ∀ current ∈ Icc 0 horizon, |unstable current| ≤ radius ∧ |stable current| ≤ radius)
    (forcingEstimate : ∀ current ∈ Icc 0 horizon,
      |unstableForcing current| + |stableForcing current| ≤
        quadratic * (|unstable current| + |stable current|) ^ 2 + forcingBound) :
    ∀ time ∈ Icc 0 horizon, |unstable time| + |stable time| ≤
      2 * (2 * forcingBound / decay + radius * Real.exp (-(decay / 2) * (horizon - time))) := by
  let feedback := 2 * quadratic * radius
  have feedbackNonnegative : 0 ≤ feedback := by dsimp only [feedback]; positivity
  have linearizedForcing : ∀ current ∈ Icc 0 horizon,
      |unstableForcing current| + |stableForcing current| ≤ forcingBound +
        feedback * (|unstable current| + |stable current|) := by
    intro current membership
    have bootstrapAt := bootstrap current membership
    have sumNonnegative : 0 ≤ |unstable current| + |stable current| := by positivity
    have squareBound : (|unstable current| + |stable current|) ^ 2 ≤
        (2 * radius) * (|unstable current| + |stable current|) := by nlinarith
    have estimate := mul_le_mul_of_nonneg_left squareBound quadraticNonnegative
    have sourceBound := forcingEstimate current membership
    dsimp only [feedback]
    nlinarith
  have ratioBound : feedback * (2 / (decay - decay / 2)) ≤ 1 / 2 := by
    have identity : feedback * (2 / (decay - decay / 2)) = 8 * quadratic * radius / decay := by
      dsimp only [feedback]
      rw [show decay - decay / 2 = decay / 2 by ring]
      field_simp [decayPositive.ne']
      <;> ring
    rw [identity]
    apply (div_le_iff₀ decayPositive).mpr
    nlinarith
  have denominatorPositive : 0 < 1 - feedback * (2 / (decay - decay / 2)) := by linarith
  have prefactorBound : 1 / (1 - feedback * (2 / (decay - decay / 2))) ≤ 2 := by
    apply (div_le_iff₀ denominatorPositive).mpr
    linarith
  have integralInequality : ∀ time ∈ Icc 0 horizon,
      |unstable time| + |stable time| ≤
        1 * (2 * forcingBound / decay + radius * Real.exp (-(decay / 2) * (horizon - time))) +
          feedback * ∫ current in (0 : ℝ)..horizon,
            Real.exp (-decay * |time - current|) * (|unstable current| + |stable current|) := by
    intro time inside
    have estimate := EulerNonuniqueness.variable_saddle_integral_bound decayPositive rateContinuous
      unstableContinuous stableContinuous unstableForcingContinuous stableForcingContinuous
      rateLower unstableEquation stableEquation stableInitial
      (bootstrap horizon ⟨horizonNonnegative, le_rfl⟩).1 forcingNonnegative feedbackNonnegative
      linearizedForcing inside
    have tailBound : Real.exp (-decay * (horizon - time)) ≤ Real.exp (-(decay / 2) * (horizon - time)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [inside.2]
    have terminalBound := mul_le_mul_of_nonneg_left tailBound radiusPositive.le
    linarith
  have tube := EulerNonuniqueness.twoSided_terminal_tube_bound
    (trajectory := fun time => |unstable time| + |stable time|)
    (base := 2 * forcingBound / decay) (terminal := radius) (initial := 1)
    horizonNonnegative (unstableContinuous.abs.add stableContinuous.abs)
    (fun time _ => by positivity) (by positivity) (by linarith)
    (by positivity) radiusPositive.le (by positivity) feedbackNonnegative
    (by linarith [ratioBound]) integralInequality
  intro time inside
  exact (tube time inside).trans
    (mul_le_mul_of_nonneg_right prefactorBound (by positivity))

end EulerNonuniqueness.Section5
