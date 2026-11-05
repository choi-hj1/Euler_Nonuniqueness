import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

namespace EulerNonuniqueness.Paper

theorem PrescribedCascadePhases.packet_phase_residual
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (index : ℕ) (indexPositive : 1 ≤ index) (nonterminal : index < count)
    (start outgoingPhase : ℝ) :
    ∃ winding : ℤ,
      (-2 * (phase index - scales.omega index * start) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi) =
        2 * scales.omega index * (start - scales.predictedTime sectionTime count (index + 1)) +
          2 * (dipoleAngle (index + 1) - outgoingPhase) := by
  obtain ⟨winding, equality⟩ := (prescribed index indexPositive nonterminal).1
  refine ⟨-winding, ?_⟩
  push_cast
  linear_combination -2 * equality

theorem PrescribedCascadePhases.packet_phase_residual_bound
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (index : ℕ) (indexPositive : 1 ≤ index) (nonterminal : index < count)
    (start outgoingPhase timingError angleError : ℝ)
    (frequencyNonnegative : 0 ≤ scales.omega index)
    (timingClose : |start - scales.predictedTime sectionTime count (index + 1)| ≤ timingError)
    (angleClose : |dipoleAngle (index + 1) - outgoingPhase| ≤ angleError) :
    ∃ winding : ℤ,
      |(-2 * (phase index - scales.omega index * start) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi)| ≤
        2 * scales.omega index * timingError + 2 * angleError := by
  obtain ⟨winding, identity⟩ := prescribed.packet_phase_residual index indexPositive nonterminal start outgoingPhase
  refine ⟨winding, ?_⟩
  rw [identity]
  apply (abs_add _ _).trans
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * scales.omega index), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact add_le_add (mul_le_mul_of_nonneg_left timingClose (by positivity))
    (mul_le_mul_of_nonneg_left angleClose (by norm_num))

end EulerNonuniqueness.Paper
