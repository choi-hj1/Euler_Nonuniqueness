import EulerNonuniqueness.Section6.SourcePacketPhaseRobustModel
import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison
import EulerNonuniqueness.Section6.SourcePacketPrescribedPhaseResidual

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_actual_source_packet_phase_robust_signed_tail :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count} {start horizon : ℝ},
    ∀ geometry : SourcePacketPhysicalGeometry family scales source start horizon radius,
    ∀ receiverRadius receiverPhase outgoingPhase tolerance : ℝ, receiverRadius ≠ 0 → 0 ≤ horizon → 0 ≤ tolerance →
    let frequency := scales.omega source.val
    let circulation := scales.circulation (source.val + 1)
    let displacement := geometry.frozenDisplacement
    let initialMoment := ∫ position, quadrupoleDensity scales family.patchMotion start source position •
      (position - quadrupoleCenter family.patchMotion start source) ^ 2
    let decay := 2 * Real.sqrt 2 * frequency
    let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * ‖displacement‖ ^ 4)
    (∀ elapsed, geometry.targetMoment elapsed = initialMoment + separatingLeadingMoment circulation outgoingPhase elapsed) →
    (∀ elapsed, geometry.idealPositive elapsed = (receiverRadius : ℂ) *
      Complex.exp (Complex.I * (receiverPhase - frequency * elapsed : ℝ))) →
    (∃ winding : ℤ, |(4 * Complex.arg displacement - 2 * receiverPhase - 2 * outgoingPhase +
      Real.arctan (1 / Real.sqrt 2) - Real.pi) - (winding : ℝ) * (2 * Real.pi)| ≤ tolerance) →
    6 * ‖initialMoment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay) ≤ seed / 8 →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) volume 0 horizon →
    ∃ packetCoefficient : ℝ,
      ((7 / 8 : ℝ) - tolerance ^ 2 / 2) * seed ≤ packetCoefficient ∧ packetCoefficient ≤ (9 / 8 : ℝ) * seed ∧
      IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.actualInput elapsed) volume 0 horizon ∧
      |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) - packetCoefficient| ≤
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) +
          17 * seed * Real.exp (-(3 * decay / 4) * horizon) := by
  obtain ⟨constant, nonnegative, radius, positive, comparison⟩ := exists_source_packet_signed_physical_comparison
  refine ⟨constant, nonnegative, radius, positive, ?_⟩
  intro count family scales source start horizon geometry receiverRadius receiverPhase outgoingPhase tolerance receiverNonzero
    horizonNonnegative toleranceNonnegative
  dsimp only
  intro targetEquation positiveEquation alignment momentSmall physicalIntegrable
  let frequency := scales.omega source.val
  let circulation := scales.circulation (source.val + 1)
  let displacement := geometry.frozenDisplacement
  let initialMoment := ∫ position, quadrupoleDensity scales family.patchMotion start source position •
    (position - quadrupoleCenter family.patchMotion start source) ^ 2
  let decay := 2 * Real.sqrt 2 * frequency
  let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * ‖displacement‖ ^ 4)
  let residual := 4 * Complex.arg displacement - 2 * receiverPhase - 2 * outgoingPhase +
    Real.arctan (1 / Real.sqrt 2) - Real.pi
  let positive := fun elapsed => (receiverRadius : ℂ) * Complex.exp (Complex.I * (receiverPhase - frequency * elapsed : ℝ))
  let packet := fun elapsed => Real.cos residual * idealGrowingInput frequency seed elapsed +
    Real.sin residual * idealQuadratureInput frequency seed elapsed + rhombusConstantMomentInput positive initialMoment displacement elapsed
  have frequencyPositive : 0 < frequency := scales.omega_pos geometry.frequencyPositive geometry.ratioPositive _
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr receiverNonzero) (Complex.exp_ne_zero _)
  have modelEquation (elapsed : ℝ) : geometry.modelInput elapsed = packet elapsed := by
    unfold SourcePacketPhysicalGeometry.modelInput
    rw [targetEquation, show geometry.idealPositive = positive from funext positiveEquation]
    have model := retained_moment_model_input_eq_packet initialMoment displacement receiverRadius frequency circulation
      receiverPhase outgoingPhase elapsed geometry.frozenNonzero
    change rhombusConstantMomentInput positive (initialMoment + separatingLeadingMoment circulation outgoingPhase elapsed) displacement elapsed = packet elapsed
    rw [model, rotatingRhombusGrowingStrainInput_phase_decomposition receiverNonzero frequency circulation ‖displacement‖
      (Complex.arg displacement) receiverPhase outgoingPhase elapsed frequencyPositive (norm_pos_iff.mpr geometry.frozenNonzero)]
  have packetContinuous : Continuous packet := by
    dsimp only [packet]
    apply Continuous.add
    · apply Continuous.add
      · exact continuous_const.mul (idealGrowingInput_continuous frequency seed)
      · unfold idealQuadratureInput
        fun_prop
    · exact rhombusConstantMomentInput_continuous positiveContinuous positiveNonzero initialMoment displacement
  have modelIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.modelInput elapsed)
      volume 0 horizon := by
    simp_rw [modelEquation]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul packetContinuous).intervalIntegrable _ _
  obtain ⟨actualIntegrable, errorBound⟩ := comparison geometry horizonNonnegative physicalIntegrable modelIntegrable
  have direct := phase_retained_moment_packet_tail positiveContinuous positiveNonzero initialMoment displacement
    (offset := residual) frequencyPositive seedNonnegative horizonNonnegative momentSmall
  let packetCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
  obtain ⟨winding, residualBound⟩ := alignment
  have cosineLower := cos_lower_of_wrapped_phase_bound winding toleranceNonnegative residualBound
  have multiplied := mul_le_mul_of_nonneg_left cosineLower seedNonnegative
  refine ⟨packetCoefficient, ?_, direct.2.1, actualIntegrable, ?_⟩
  · have lower := (abs_le.mp direct.1).1
    change -(seed / 8) ≤ packetCoefficient - seed * Real.cos residual at lower
    nlinarith only [lower, multiplied]
  have triangle := abs_sub_le
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed)
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed) packetCoefficient
  have packetBound : |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed) -
      packetCoefficient| ≤ 17 * seed * Real.exp (-(3 * decay / 4) * horizon) := by
    simp_rw [modelEquation]
    exact direct.2.2
  exact triangle.trans (add_le_add errorBound packetBound)

end EulerNonuniqueness.Paper
