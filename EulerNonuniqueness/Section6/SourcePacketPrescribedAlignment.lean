import EulerNonuniqueness.Section6.SourcePacketPrescribedPhaseResidual
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.adjacent_frozen_displacement_arg (scales : Scales) (index : ℕ) :
    Complex.arg ((scales.location index : ℂ) - (scales.location (index + 1) : ℂ)) = 0 := by
  rw [← Complex.ofReal_sub]
  apply Complex.arg_ofReal_of_nonneg
  exact sub_nonneg.mpr (scales.location_antitone (Nat.le_succ index))

theorem PrescribedCascadePhases.adjacent_packet_alignment_bound
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (index : ℕ) (indexPositive : 1 ≤ index) (nonterminal : index < count)
    (start outgoingPhase timingError angleError : ℝ)
    (frequencyNonnegative : 0 ≤ scales.omega index)
    (timingClose : |start - scales.predictedTime sectionTime count (index + 1)| ≤ timingError)
    (angleClose : |dipoleAngle (index + 1) - outgoingPhase| ≤ angleError) :
    ∃ winding : ℤ,
      |(4 * Complex.arg ((scales.location index : ℂ) - (scales.location (index + 1) : ℂ)) -
          2 * (phase index - scales.omega index * start) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi)| ≤
        2 * scales.omega index * timingError + 2 * angleError := by
  simpa only [scales.adjacent_frozen_displacement_arg, mul_zero, zero_sub, neg_mul] using
    prescribed.packet_phase_residual_bound index indexPositive nonterminal start outgoingPhase timingError angleError
      frequencyNonnegative timingClose angleClose

theorem PrescribedCascadePhases.adjacent_packet_alignment_source_time_bound
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (index : ℕ) (indexPositive : 1 ≤ index) (nonterminal : index < count)
    (start outgoingPhase timingConstant tolerance angleError : ℝ)
    (timingClose : |start - scales.predictedTime sectionTime count (index + 1)| ≤
      timingConstant * tolerance / scales.omega (index + 1))
    (angleClose : |dipoleAngle (index + 1) - outgoingPhase| ≤ angleError) :
    ∃ winding : ℤ,
      |(4 * Complex.arg ((scales.location index : ℂ) - (scales.location (index + 1) : ℂ)) -
          2 * (phase index - scales.omega index * start) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi)| ≤
        2 * timingConstant * tolerance / scales.ratio + 2 * angleError := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  obtain ⟨winding, bounded⟩ := prescribed.adjacent_packet_alignment_bound index indexPositive nonterminal start outgoingPhase
    (timingConstant * tolerance / scales.omega (index + 1)) angleError omegaPositive.le timingClose angleClose
  refine ⟨winding, bounded.trans_eq ?_⟩
  congr 1
  unfold Scales.omega
  rw [pow_succ]
  field_simp [frequencyPositive.ne', ratioPositive.ne', pow_ne_zero index ratioPositive.ne']
  <;> ring

theorem PrescribedCascadePhases.adjacent_packet_alignment_modulo_angle_bound
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (index : ℕ) (indexPositive : 1 ≤ index) (nonterminal : index < count)
    (start outgoingPhase timingError angleError : ℝ)
    (frequencyNonnegative : 0 ≤ scales.omega index)
    (timingClose : |start - scales.predictedTime sectionTime count (index + 1)| ≤ timingError)
    (angleClose : ∃ winding : ℤ, |dipoleAngle (index + 1) - outgoingPhase - (winding : ℝ) * Real.pi| ≤ angleError) :
    ∃ winding : ℤ,
      |(4 * Complex.arg ((scales.location index : ℂ) - (scales.location (index + 1) : ℂ)) -
          2 * (phase index - scales.omega index * start) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi)| ≤
        2 * scales.omega index * timingError + 2 * angleError := by
  obtain ⟨firstWinding, identity⟩ := prescribed.packet_phase_residual index indexPositive nonterminal start outgoingPhase
  obtain ⟨angleWinding, angleBound⟩ := angleClose
  refine ⟨firstWinding + angleWinding, ?_⟩
  rw [scales.adjacent_frozen_displacement_arg, mul_zero, zero_sub]
  have combined :
      (-(2 * (phase index - scales.omega index * start)) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - ((firstWinding + angleWinding : ℤ) : ℝ) * (2 * Real.pi) =
        2 * scales.omega index * (start - scales.predictedTime sectionTime count (index + 1)) +
          2 * (dipoleAngle (index + 1) - outgoingPhase - (angleWinding : ℝ) * Real.pi) := by
    push_cast
    linear_combination identity
  rw [combined]
  apply (abs_add _ _).trans
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * scales.omega index), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact add_le_add (mul_le_mul_of_nonneg_left timingClose (by positivity))
    (mul_le_mul_of_nonneg_left angleBound (by norm_num))

theorem PrescribedCascadePhases.adjacent_packet_alignment_modulo_source_time_bound
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (index : ℕ) (indexPositive : 1 ≤ index) (nonterminal : index < count)
    (start outgoingPhase timingConstant tolerance angleError : ℝ)
    (timingClose : |start - scales.predictedTime sectionTime count (index + 1)| ≤
      timingConstant * tolerance / scales.omega (index + 1))
    (angleClose : ∃ winding : ℤ, |dipoleAngle (index + 1) - outgoingPhase - (winding : ℝ) * Real.pi| ≤ angleError) :
    ∃ winding : ℤ,
      |(4 * Complex.arg ((scales.location index : ℂ) - (scales.location (index + 1) : ℂ)) -
          2 * (phase index - scales.omega index * start) - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi)| ≤
        2 * timingConstant * tolerance / scales.ratio + 2 * angleError := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  obtain ⟨winding, bounded⟩ := prescribed.adjacent_packet_alignment_modulo_angle_bound index indexPositive nonterminal start outgoingPhase
    (timingConstant * tolerance / scales.omega (index + 1)) angleError omegaPositive.le timingClose angleClose
  refine ⟨winding, bounded.trans_eq ?_⟩
  congr 1
  unfold Scales.omega
  rw [pow_succ]
  field_simp [frequencyPositive.ne', ratioPositive.ne', pow_ne_zero index ratioPositive.ne']
  <;> ring

end EulerNonuniqueness.Paper
