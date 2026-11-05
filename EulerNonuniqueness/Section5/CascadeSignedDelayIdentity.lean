import EulerNonuniqueness.Section5.CascadeProof
import EulerNonuniqueness.Section5.Delay
import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.signed_delay_identity (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {count index : ℕ} (nonterminal : index < count)
    (sectionTime origin hit contact level coefficient : ℝ)
    (levelPositive : 0 < level) (coefficientPositive : 0 < coefficient)
    (exitIdentity : scales.seed index * coefficient *
      Real.exp ((2 * Real.sqrt 2 * scales.omega index) * (hit - origin)) = level) :
    scales.omega index * (contact - scales.predictedTime sectionTime count index) -
      scales.ratio⁻¹ * (scales.omega (index + 1) *
        (origin - scales.predictedTime sectionTime count (index + 1))) +
      Real.log coefficient / (2 * Real.sqrt 2) =
    scales.omega index * (contact - hit) - sectionTime + Real.log level / (2 * Real.sqrt 2) := by
  have seedPositive := scales.seed_pos frequencyPositive ratioPositive index
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have denominatorPositive : 0 < 2 * Real.sqrt (2 : ℝ) := by positivity
  have growthPositive : 0 < 2 * Real.sqrt 2 * scales.omega index := by positivity
  have logarithmic := Section6.exponential_exit_time growthPositive
    (mul_pos seedPositive coefficientPositive) exitIdentity
  have hitIdentity : scales.omega index * (hit - origin) =
      (Real.log level - Real.log (scales.seed index) - Real.log coefficient) / (2 * Real.sqrt 2) := by
    rw [logarithmic, Real.log_div levelPositive.ne' (mul_pos seedPositive coefficientPositive).ne',
      Real.log_mul seedPositive.ne' coefficientPositive.ne']
    field_simp
    ring
  have delayIdentity : scales.omega index * scales.delay sectionTime index =
      Real.log (1 / scales.seed index) / (2 * Real.sqrt 2) + sectionTime := by
    unfold Scales.delay
    field_simp
    ring
  have recurrence : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have sourceIdentity : scales.ratio⁻¹ * (scales.omega (index + 1) *
      (origin - scales.predictedTime sectionTime count (index + 1))) =
      scales.omega index * (origin - scales.predictedTime sectionTime count (index + 1)) := by
    rw [recurrence]
    field_simp
    ring
  rw [scales.predictedTime_step sectionTime nonterminal, sourceIdentity]
  calc
    _ = scales.omega index * (contact - hit) + scales.omega index * (hit - origin) -
        scales.omega index * scales.delay sectionTime index + Real.log coefficient / (2 * Real.sqrt 2) := by ring
    _ = _ := by
      rw [hitIdentity, delayIdentity, Real.log_div one_ne_zero seedPositive.ne', Real.log_one]
      ring

end EulerNonuniqueness.Paper
