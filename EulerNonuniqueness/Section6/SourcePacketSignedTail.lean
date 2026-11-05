import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison
import EulerNonuniqueness.Section6.SourcePacketRetainedModel

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_actual_source_packet_signed_tail :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count} {start horizon : ℝ},
    ∀ geometry : SourcePacketPhysicalGeometry family scales source start horizon radius,
    ∀ receiverRadius receiverPhase outgoingPhase : ℝ, receiverRadius ≠ 0 → 0 ≤ horizon →
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
    4 * Complex.arg displacement - 2 * receiverPhase - 2 * outgoingPhase = Real.pi - Real.arctan (1 / Real.sqrt 2) →
    6 * ‖initialMoment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay) ≤ seed / 8 →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) volume 0 horizon →
    ∃ packetCoefficient : ℝ,
      (7 / 8 : ℝ) * seed ≤ packetCoefficient ∧ packetCoefficient ≤ (9 / 8 : ℝ) * seed ∧
      IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.actualInput elapsed) volume 0 horizon ∧
      |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) - packetCoefficient| ≤
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) +
          9 * seed * Real.exp (-(3 * decay / 4) * horizon) := by
  obtain ⟨constant, nonnegative, radius, positive, comparison⟩ := exists_source_packet_signed_physical_comparison
  refine ⟨constant, nonnegative, radius, positive, ?_⟩
  intro count family scales source start horizon geometry receiverRadius receiverPhase outgoingPhase receiverNonzero horizonNonnegative
  dsimp only
  intro targetEquation positiveEquation phaseAlignment momentSmall physicalIntegrable
  let frequency := scales.omega source.val
  let circulation := scales.circulation (source.val + 1)
  let displacement := geometry.frozenDisplacement
  let initialMoment := ∫ position, quadrupoleDensity scales family.patchMotion start source position •
    (position - quadrupoleCenter family.patchMotion start source) ^ 2
  let decay := 2 * Real.sqrt 2 * frequency
  let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * ‖displacement‖ ^ 4)
  let positive := fun elapsed => (receiverRadius : ℂ) * Complex.exp (Complex.I * (receiverPhase - frequency * elapsed : ℝ))
  let packet := fun elapsed => idealGrowingInput frequency seed elapsed +
    rhombusConstantMomentInput positive initialMoment displacement elapsed
  have frequencyPositive : 0 < frequency := scales.omega_pos geometry.frequencyPositive geometry.ratioPositive _
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr receiverNonzero) (Complex.exp_ne_zero _)
  have modelEquation (elapsed : ℝ) : geometry.modelInput elapsed = packet elapsed := by
    unfold SourcePacketPhysicalGeometry.modelInput
    rw [targetEquation]
    have positiveIdentity : geometry.idealPositive = positive := funext positiveEquation
    rw [positiveIdentity]
    have model := retained_moment_model_input_eq_packet initialMoment displacement receiverRadius frequency circulation
      receiverPhase outgoingPhase elapsed geometry.frozenNonzero
    have growing := rotatingRhombusGrowingStrainInput_maximizing_eq
      (circulation := circulation) receiverNonzero frequencyPositive (norm_pos_iff.mpr geometry.frozenNonzero)
      phaseAlignment elapsed
    change rhombusConstantMomentInput positive
      (initialMoment + separatingLeadingMoment circulation outgoingPhase elapsed) displacement elapsed = packet elapsed
    rw [model, growing]
  have packetContinuous : Continuous packet :=
    (idealGrowingInput_continuous frequency seed).add
      (rhombusConstantMomentInput_continuous positiveContinuous positiveNonzero initialMoment displacement)
  have modelIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.modelInput elapsed)
      volume 0 horizon := by
    simp_rw [modelEquation]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul packetContinuous).intervalIntegrable _ _
  obtain ⟨actualIntegrable, errorBound⟩ := comparison geometry horizonNonnegative physicalIntegrable modelIntegrable
  have direct := ideal_retained_moment_packet_direct_tail positiveContinuous positiveNonzero initialMoment displacement
    frequencyPositive seedNonnegative horizonNonnegative momentSmall
  let packetCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
  refine ⟨packetCoefficient, direct.1, direct.2.1, actualIntegrable, ?_⟩
  have triangle := abs_sub_le
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed)
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed) packetCoefficient
  have packetBound : |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed) -
      packetCoefficient| ≤ 9 * seed * Real.exp (-(3 * decay / 4) * horizon) := by
    simp_rw [modelEquation]
    exact direct.2.2
  exact triangle.trans (add_le_add errorBound packetBound)

end EulerNonuniqueness.Paper
