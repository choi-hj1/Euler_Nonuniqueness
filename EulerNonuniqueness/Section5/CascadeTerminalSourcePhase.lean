import EulerNonuniqueness.Section5.CascadeProof
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

/-- The prescribed phases make the terminal source's actual frozen-bearing residual exactly maximizing. -/
theorem PrescribedCascadePhases.terminal_source_residual_cos
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (receiver source : Fin count) (adjacent : receiver.val + 1 = source.val)
    (terminal : source.val + 1 = count) :
    Real.cos (4 * Complex.arg ((scales.location (receiver.val + 1) : ℂ) -
      (scales.location (source.val + 1) : ℂ)) - 2 * phase (receiver.val + 1) -
      2 * dipoleAngle count + Real.arctan (1 / Real.sqrt 2) - Real.pi) = 1 := by
  have next : receiver.val + 1 + 1 = count := by omega
  obtain ⟨winding, phaseEquation⟩ :=
    (prescribed (receiver.val + 1) (by omega) (by omega)).1
  rw [next, scales.predictedTime_terminal, mul_zero, zero_add] at phaseEquation
  have ordered : receiver.val + 1 < source.val + 1 := by omega
  have locationBound := scales.location_le_half_of_lt ordered
  have bearing : Complex.arg ((scales.location (receiver.val + 1) : ℂ) -
      (scales.location (source.val + 1) : ℂ)) = 0 := by
    rw [← Complex.ofReal_sub]
    apply Complex.arg_ofReal_of_nonneg
    linarith only [locationBound, (scales.location_pos (receiver.val + 1)).le]
  rw [bearing]
  have residual : 4 * (0 : ℝ) - 2 * phase (receiver.val + 1) - 2 * dipoleAngle count +
      Real.arctan (1 / Real.sqrt 2) - Real.pi = ((-winding : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linarith only [phaseEquation]
  rw [residual]
  exact Real.cos_int_mul_two_pi (-winding)

end EulerNonuniqueness.Paper
