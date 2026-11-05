import EulerNonuniqueness.General.CorrectedLogCosTiming
import EulerNonuniqueness.Section5.CascadeSignedDelayIdentity

noncomputable section
namespace EulerNonuniqueness.Paper

/-- Actual exit and passage identities give the timing recurrence without assuming the current timing error small. -/
theorem Scales.actual_exit_timing_recurrence (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioLarge : 4 ≤ scales.ratio)
    {count index : ℕ} (nonterminal : index < count)
    (sectionTime origin hit contact incomingTime level coefficient coefficientError phaseError passageError modelError : ℝ)
    (levelPositive : 0 < level) (coefficientPositive : 0 < coefficient)
    (exitIdentity : scales.seed index * coefficient *
      Real.exp ((2 * Real.sqrt 2 * scales.omega index) * (hit - origin)) = level)
    (coefficientErrorNonnegative : 0 ≤ coefficientError)
    (effectiveSmall : coefficientError + 2 * |phaseError| ≤ 1 / 8)
    (passageBound : |scales.omega index * (contact - hit) - (sectionTime - incomingTime)| ≤ passageError)
    (modelBound : |Real.log level / (2 * Real.sqrt 2) - incomingTime| ≤ modelError) :
    let next := scales.omega (index + 1) * (origin - scales.predictedTime sectionTime count (index + 1))
    |2 * (1 + scales.ratio⁻¹) * next| ≤ 1 / 2 →
    |coefficient - Real.cos (2 * (1 + scales.ratio⁻¹) * next - 2 * phaseError)| ≤ coefficientError →
    |scales.omega index * (contact - scales.predictedTime sectionTime count index)| ≤
      scales.ratio⁻¹ * |next| + 4 * next ^ 2 + coefficientError + 2 * |phaseError| + passageError + modelError := by
  dsimp only
  intro angleSmall coefficientClose
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioLarge]
  have identity := scales.signed_delay_identity frequencyPositive ratioPositive nonterminal
    sectionTime origin hit contact level coefficient levelPositive coefficientPositive exitIdentity
  have passageNonnegative : 0 ≤ passageError := (abs_nonneg _).trans passageBound
  have modelNonnegative : 0 ≤ modelError := (abs_nonneg _).trans modelBound
  have delayBound :
      |scales.omega index * (contact - scales.predictedTime sectionTime count index) -
        scales.ratio⁻¹ * (scales.omega (index + 1) * (origin - scales.predictedTime sectionTime count (index + 1))) +
          Real.log coefficient / (2 * Real.sqrt 2)| ≤ passageError + modelError := by
    rw [identity]
    have rearrange : scales.omega index * (contact - hit) - sectionTime + Real.log level / (2 * Real.sqrt 2) =
        (scales.omega index * (contact - hit) - (sectionTime - incomingTime)) +
          (Real.log level / (2 * Real.sqrt 2) - incomingTime) := by ring
    rw [rearrange]
    exact (abs_add _ _).trans (add_le_add passageBound modelBound)
  have result := EulerNonuniqueness.corrected_log_cos_timing_recurrence ratioLarge coefficientErrorNonnegative effectiveSmall
    (add_nonneg passageNonnegative modelNonnegative) angleSmall coefficientClose delayBound
  linarith only [result]

/-- At the terminal source the next predicted time and origin are zero, and the target cosine is one. -/
theorem Scales.terminal_actual_exit_timing_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioLarge : 4 ≤ scales.ratio)
    {count index : ℕ} (terminal : index + 1 = count)
    (sectionTime hit contact incomingTime level coefficient coefficientError passageError modelError : ℝ)
    (levelPositive : 0 < level) (coefficientPositive : 0 < coefficient)
    (exitIdentity : scales.seed index * coefficient * Real.exp ((2 * Real.sqrt 2 * scales.omega index) * hit) = level)
    (coefficientErrorNonnegative : 0 ≤ coefficientError) (coefficientErrorSmall : coefficientError ≤ 1 / 8)
    (coefficientClose : |coefficient - 1| ≤ coefficientError)
    (passageBound : |scales.omega index * (contact - hit) - (sectionTime - incomingTime)| ≤ passageError)
    (modelBound : |Real.log level / (2 * Real.sqrt 2) - incomingTime| ≤ modelError) :
    |scales.omega index * (contact - scales.predictedTime sectionTime count index)| ≤ coefficientError + passageError + modelError := by
  have nonterminal : index < count := by omega
  have predicted : scales.predictedTime sectionTime count (index + 1) = 0 := by
    rw [terminal, scales.predictedTime_terminal]
  have result := scales.actual_exit_timing_recurrence frequencyPositive ratioLarge nonterminal
    sectionTime 0 hit contact incomingTime level coefficient coefficientError 0 passageError modelError levelPositive coefficientPositive
    (by simpa only [sub_zero] using exitIdentity) coefficientErrorNonnegative
    (by simpa only [abs_zero, mul_zero, add_zero] using coefficientErrorSmall) passageBound modelBound
    (by simp only [predicted, sub_self, mul_zero, abs_zero]; norm_num)
    (by simpa only [predicted, sub_self, mul_zero, sub_zero, Real.cos_zero] using coefficientClose)
  simpa only [predicted, sub_self, mul_zero, abs_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, add_zero] using result

end EulerNonuniqueness.Paper
