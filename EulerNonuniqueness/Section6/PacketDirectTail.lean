import EulerNonuniqueness.Section6.RetainedMomentPacketTail

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem laplace_packet_fractional_tail_bound {frequency coefficient momentCost terminal : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (costNonnegative : 0 ≤ momentCost) (terminalNonnegative : 0 ≤ terminal) :
    Real.exp (-(2 * Real.sqrt 2 * frequency) * terminal) *
        (coefficient * (1 + 2 * Real.sqrt 3 * frequency * terminal) + momentCost) ≤
      8 * (coefficient + momentCost) * Real.exp (-(3 * (2 * Real.sqrt 2 * frequency) / 4) * terminal) := by
  have productNonnegative : 0 ≤ frequency * terminal := mul_nonneg frequencyNonnegative terminalNonnegative
  have sqrtTwoLower : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThreeUpper : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have scaledTwo := mul_le_mul_of_nonneg_right sqrtTwoLower productNonnegative
  have scaledThree := mul_le_mul_of_nonneg_right sqrtThreeUpper productNonnegative
  have polynomial : 1 + 2 * Real.sqrt 3 * frequency * terminal ≤
      8 * (1 + (Real.sqrt 2 / 2) * (frequency * terminal)) := by nlinarith only [scaledTwo, scaledThree]
  have exponential := Real.add_one_le_exp ((Real.sqrt 2 / 2) * (frequency * terminal))
  have growing : 1 + 2 * Real.sqrt 3 * frequency * terminal ≤
      8 * Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal)) :=
    polynomial.trans (by simpa only [add_comm] using mul_le_mul_of_nonneg_left exponential (by norm_num : (0 : ℝ) ≤ 8))
  have expOne : 1 ≤ Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal)) := Real.one_le_exp (by positivity)
  have constantBound : momentCost ≤ 8 * momentCost * Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal)) := by
    have actual := mul_le_mul_of_nonneg_left expOne costNonnegative
    nlinarith only [actual, costNonnegative]
  have bracket := add_le_add (mul_le_mul_of_nonneg_left growing coefficientNonnegative) constantBound
  have multiplied := mul_le_mul_of_nonneg_left bracket (Real.exp_pos (-(2 * Real.sqrt 2 * frequency) * terminal)).le
  have identity : Real.exp (-(2 * Real.sqrt 2 * frequency) * terminal) * Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal)) =
      Real.exp (-(3 * (2 * Real.sqrt 2 * frequency) / 4) * terminal) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (-(2 * Real.sqrt 2 * frequency) * terminal) *
        (coefficient * (8 * Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal))) +
          8 * momentCost * Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal))) := multiplied
    _ = 8 * (coefficient + momentCost) *
        (Real.exp (-(2 * Real.sqrt 2 * frequency) * terminal) * Real.exp ((Real.sqrt 2 / 2) * (frequency * terminal))) := by ring
    _ = _ := by rw [identity]

theorem ideal_retained_moment_packet_direct_tail {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {frequency coefficient terminal : ℝ}
    (frequencyPositive : 0 < frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (terminalNonnegative : 0 ≤ terminal)
    (smallInitialMoment : 6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * (2 * Real.sqrt 2 * frequency)) ≤ coefficient / 8) :
    let decay := 2 * Real.sqrt 2 * frequency
    let input := fun elapsed => idealGrowingInput frequency coefficient elapsed + rhombusConstantMomentInput positive moment displacement elapsed
    let packetCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * input elapsed
    (7 / 8 : ℝ) * coefficient ≤ packetCoefficient ∧ packetCoefficient ≤ (9 / 8 : ℝ) * coefficient ∧
      |(∫ elapsed in (0 : ℝ)..terminal, Real.exp (-decay * elapsed) * input elapsed) - packetCoefficient| ≤
        9 * coefficient * Real.exp (-(3 * decay / 4) * terminal) := by
  have actual := ideal_retained_moment_packet_tail continuous nonzero moment displacement frequencyPositive coefficientNonnegative terminalNonnegative
  dsimp only at actual ⊢
  refine ⟨by linarith only [(abs_le.mp actual.1).1, smallInitialMoment],
    by linarith only [(abs_le.mp actual.1).2, smallInitialMoment], ?_⟩
  apply actual.2.trans
  apply (laplace_packet_fractional_tail_bound frequencyPositive.le coefficientNonnegative (by positivity) terminalNonnegative).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  linarith only [smallInitialMoment]

end EulerNonuniqueness.Section6
