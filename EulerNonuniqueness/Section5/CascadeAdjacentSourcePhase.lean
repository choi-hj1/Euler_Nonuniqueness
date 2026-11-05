import EulerNonuniqueness.Section6.SourcePacketPrescribedPhaseResidual
import EulerNonuniqueness.Section6.SourcePacketPhaseRobustModel
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

theorem PrescribedCascadePhases.adjacent_source_phase_cos_eq
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (ratioNonzero : scales.ratio ≠ 0)
    (receiver source : Fin count) (adjacent : receiver.val + 1 = source.val)
    (start outgoingPhase : ℝ) (sourceWinding : ℤ) :
    let timingShift := scales.omega (source.val + 1) *
      (start - scales.predictedTime sectionTime count (source.val + 1))
    let phaseError := outgoingPhase - dipoleAngle (source.val + 1) + timingShift -
      (sourceWinding : ℝ) * Real.pi
    Real.cos (4 * Complex.arg ((scales.location (receiver.val + 1) : ℂ) -
      (scales.location (source.val + 1) : ℂ)) -
      2 * (phase (receiver.val + 1) - scales.omega (receiver.val + 1) * start) -
      2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi) =
    Real.cos (2 * (1 + scales.ratio⁻¹) * timingShift - 2 * phaseError) := by
  dsimp only
  have next : receiver.val + 1 + 1 = source.val + 1 := by omega
  obtain ⟨winding, identity⟩ := prescribed.packet_phase_residual (receiver.val + 1)
    (by omega) (by omega) start outgoingPhase
  rw [next] at identity
  have recurrence : scales.omega (source.val + 1) = scales.omega (receiver.val + 1) * scales.ratio := by
    rw [← adjacent]
    simp only [Scales.omega, pow_succ]
    ring
  have scaled : scales.ratio⁻¹ * (scales.omega (source.val + 1) *
      (start - scales.predictedTime sectionTime count (source.val + 1))) =
      scales.omega (receiver.val + 1) *
        (start - scales.predictedTime sectionTime count (source.val + 1)) := by
    rw [recurrence]
    field_simp
    ring
  have bearing : Complex.arg ((scales.location (receiver.val + 1) : ℂ) -
      (scales.location (source.val + 1) : ℂ)) = 0 := by
    have ordered : receiver.val + 1 < source.val + 1 := by omega
    have distance := scales.location_le_half_of_lt ordered
    rw [← Complex.ofReal_sub]
    apply Complex.arg_ofReal_of_nonneg
    linarith only [distance, (scales.location_pos (receiver.val + 1)).le]
  rw [bearing]
  have residualIdentity :
      (4 * (0 : ℝ) - 2 * (phase (receiver.val + 1) - scales.omega (receiver.val + 1) * start) -
        2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi) -
        ((winding - sourceWinding : ℤ) : ℝ) * (2 * Real.pi) =
      2 * (1 + scales.ratio⁻¹) *
        (scales.omega (source.val + 1) * (start - scales.predictedTime sectionTime count (source.val + 1))) -
        2 * (outgoingPhase - dipoleAngle (source.val + 1) +
          scales.omega (source.val + 1) * (start - scales.predictedTime sectionTime count (source.val + 1)) -
          (sourceWinding : ℝ) * Real.pi) := by
    push_cast
    linear_combination identity - 2 * scaled
  rw [← residualIdentity, Real.cos_sub_int_mul_two_pi]

theorem PrescribedCascadePhases.adjacent_source_phase_cos_lower
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {count : ℕ}
    {phase dipoleAngle : ℕ → ℝ}
    (prescribed : PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle)
    (ratioBound : 2 ≤ scales.ratio)
    (receiver source : Fin count) (adjacent : receiver.val + 1 = source.val)
    (start outgoingPhase timingBound phaseBound : ℝ) (sourceWinding : ℤ) :
    let timingShift := scales.omega (source.val + 1) *
      (start - scales.predictedTime sectionTime count (source.val + 1))
    let phaseError := outgoingPhase - dipoleAngle (source.val + 1) + timingShift -
      (sourceWinding : ℝ) * Real.pi
    |timingShift| ≤ timingBound → |phaseError| ≤ phaseBound →
    3 * timingBound + 2 * phaseBound ≤ 1 / 2 →
    (7 / 8 : ℝ) ≤ Real.cos (4 * Complex.arg ((scales.location (receiver.val + 1) : ℂ) -
      (scales.location (source.val + 1) : ℂ)) -
      2 * (phase (receiver.val + 1) - scales.omega (receiver.val + 1) * start) -
      2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi) := by
  dsimp only
  intro timingSmall phaseSmall budget
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  rw [prescribed.adjacent_source_phase_cos_eq ratioPositive.ne' receiver source adjacent start outgoingPhase sourceWinding]
  let timingShift := scales.omega (source.val + 1) *
    (start - scales.predictedTime sectionTime count (source.val + 1))
  let phaseError := outgoingPhase - dipoleAngle (source.val + 1) + timingShift -
    (sourceWinding : ℝ) * Real.pi
  let coefficient := 2 * (1 + scales.ratio⁻¹)
  have inverseHalf : scales.ratio⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ratioBound
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have coefficientThree : coefficient ≤ 3 := by dsimp only [coefficient]; linarith only [inverseHalf]
  have reducedSmall : |coefficient * timingShift - 2 * phaseError| ≤ 1 / 2 := by
    calc
      _ ≤ |coefficient * timingShift| + |2 * phaseError| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add (coefficient * timingShift) (-(2 * phaseError))
      _ = coefficient * |timingShift| + 2 * |phaseError| := by
        simp only [abs_mul, abs_of_nonneg coefficientNonnegative, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 3 * timingBound + 2 * phaseBound := add_le_add
        (mul_le_mul coefficientThree timingSmall (abs_nonneg _) (by norm_num))
        (mul_le_mul_of_nonneg_left phaseSmall (by norm_num))
      _ ≤ 1 / 2 := budget
  have square := (sq_le_sq₀ (abs_nonneg (coefficient * timingShift - 2 * phaseError))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr reducedSmall
  rw [sq_abs] at square
  have cosine := Real.one_sub_sq_div_two_le_cos (x := coefficient * timingShift - 2 * phaseError)
  change (7 / 8 : ℝ) ≤ Real.cos (coefficient * timingShift - 2 * phaseError)
  nlinarith only [cosine, square]

end EulerNonuniqueness.Paper
