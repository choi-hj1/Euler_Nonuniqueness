import EulerNonuniqueness.Section5.ReferenceInteriorTubeOn
import EulerNonuniqueness.General.ExponentialPowerTail

open Set

namespace EulerNonuniqueness.Section5

theorem reference_frequency_tube_of_actual_equations
    {rate unstable stable unstableForcing stableForcing : ℝ → ℝ}
    {frequency rateConstant radius forcingConstant strain quadratic : ℝ}
    (frequencyPositive : 0 < frequency) (rateConstantPositive : 0 < rateConstant)
    (radiusPositive : 0 < radius) (forcingConstantNonnegative : 0 ≤ forcingConstant)
    (strainNonnegative : 0 ≤ strain) (quadraticNonnegative : 0 ≤ quadratic)
    (small : 16 * quadratic * radius ≤ rateConstant * frequency)
    (rateContinuous : ContinuousOn rate (Icc 0 2))
    (unstableContinuous : ContinuousOn unstable (Icc 0 2))
    (stableContinuous : ContinuousOn stable (Icc 0 2))
    (unstableForcingContinuous : ContinuousOn unstableForcing (Icc 0 2))
    (stableForcingContinuous : ContinuousOn stableForcing (Icc 0 2))
    (rateLower : ∀ current ∈ Icc 0 2, rateConstant * frequency ≤ rate current)
    (unstableEquation : ∀ current ∈ Icc 0 2,
      HasDerivAt unstable (rate current * unstable current + unstableForcing current) current)
    (stableEquation : ∀ current ∈ Icc 0 2,
      HasDerivAt stable (-rate current * stable current + stableForcing current) current)
    (stableInitial : stable 0 = 0)
    (bootstrap : ∀ current ∈ Icc 0 2, |unstable current| ≤ radius ∧ |stable current| ≤ radius)
    (forcingEstimate : ∀ current ∈ Icc 0 2,
      |unstableForcing current| + |stableForcing current| ≤
        quadratic * (|unstable current| + |stable current|) ^ 2 +
          forcingConstant * (strain + 1 / frequency ^ 4)) :
    ∀ time ∈ Icc 0 1, |unstable time| + |stable time| ≤
      (4 * forcingConstant / rateConstant + 240 * radius / (rateConstant / 2) ^ 5) *
        (strain / frequency + 1 / frequency ^ 5) := by
  have decayPositive : 0 < rateConstant * frequency := mul_pos rateConstantPositive frequencyPositive
  have tube := reference_interior_tube_of_actual_equations_on_Icc decayPositive
    (by norm_num : (0 : ℝ) ≤ 2) radiusPositive (by positivity) quadraticNonnegative small
    rateContinuous unstableContinuous stableContinuous unstableForcingContinuous stableForcingContinuous
    rateLower unstableEquation stableEquation stableInitial bootstrap forcingEstimate
  intro time inside
  have timeInside : time ∈ Icc 0 2 := ⟨inside.1, inside.2.trans (by norm_num)⟩
  have tailBound : Real.exp (-(rateConstant * frequency / 2) * (2 - time)) ≤
      ((120 : ℝ) / (rateConstant / 2) ^ 5) / frequency ^ 5 := by
    calc
      _ ≤ Real.exp (-(rateConstant / 2) * frequency) := by
        apply Real.exp_le_exp.mpr
        nlinarith [inside.2]
      _ ≤ _ := by
        simpa only [show (((5 : ℕ).factorial : ℝ)) = 120 by norm_num] using
          EulerNonuniqueness.exp_neg_mul_le_factorial_div_pow 5
            (show 0 < rateConstant / 2 by positivity) frequencyPositive
  have sourceIdentity : 4 * (forcingConstant * (strain + 1 / frequency ^ 4)) /
      (rateConstant * frequency) = (4 * forcingConstant / rateConstant) *
        (strain / frequency + 1 / frequency ^ 5) := by
    field_simp [rateConstantPositive.ne', frequencyPositive.ne']
    <;> ring
  have estimate := tube time timeInside
  have scaledTail := mul_le_mul_of_nonneg_left tailBound radiusPositive.le
  have preliminary : |unstable time| + |stable time| ≤
      (4 * forcingConstant / rateConstant) * (strain / frequency + 1 / frequency ^ 5) +
        (240 * radius / (rateConstant / 2) ^ 5) * (1 / frequency ^ 5) := by
    rw [← sourceIdentity]
    calc
      _ ≤ 2 * (2 * (forcingConstant * (strain + 1 / frequency ^ 4)) / (rateConstant * frequency) +
          radius * Real.exp (-(rateConstant * frequency / 2) * (2 - time))) := estimate
      _ ≤ 2 * (2 * (forcingConstant * (strain + 1 / frequency ^ 4)) / (rateConstant * frequency) +
          radius * ((120 / (rateConstant / 2) ^ 5) / frequency ^ 5)) :=
        mul_le_mul_of_nonneg_left (add_le_add_left scaledTail _) (by norm_num)
      _ = _ := by ring
  have missingNonnegative : 0 ≤ (240 * radius / (rateConstant / 2) ^ 5) * (strain / frequency) := by positivity
  nlinarith [preliminary]

end EulerNonuniqueness.Section5
