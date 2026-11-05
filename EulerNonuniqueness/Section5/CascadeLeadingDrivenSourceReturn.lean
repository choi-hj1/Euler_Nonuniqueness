import EulerNonuniqueness.Section5.CascadeCoarserLeadingActualFeedback
import EulerNonuniqueness.Section6.SourcePacketActualLeadingSplit

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_leading_driven_source_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    4 < scales.ratio ^ scales.alpha → ∀ {tolerance : ℝ}, 0 < tolerance →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver adjacent : Fin count, receiver.val + 1 = adjacent.val →
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    ‖quadrupoleRelativeLeadingStrain changed alternative reference time receiver -
      relativeBlockSourceShapeInput changed alternative reference receiver adjacent time‖ ≤
      (constant / changed.location (receiver.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
          ‖fun source : Fin count => if source.val ≤ receiver.val then
            changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ +
        tolerance * changed.seed (receiver.val + 1) := by
  obtain ⟨rawCap, rawPositive, constant, constantNonnegative, coarserBounds⟩ :=
    exists_uniform_actual_coarser_leading_actual_feedback
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive ratioPower tolerance tolerancePositive orbit sectionTime
    threshold referenceConstant scaleRoot factor boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
    factorPositive factorSmall
  filter_upwards [coarserBounds scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_relative_leading_adjacent_remainder amplitudePositive ratioBound alphaPositive ratioPower
      tolerancePositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency coarser remainder
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver adjacent adjacentIdentity
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let coarserInput := ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
    relativeBlockSourceShapeInput changed alternative reference receiver source time
  let adjacentInput := relativeBlockSourceShapeInput changed alternative reference receiver adjacent time
  let leading := quadrupoleRelativeLeadingStrain changed alternative reference time receiver
  have coarserBound := coarser count phase dipoleAngle prepared path time inside receiver
  have remainderBound := remainder count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside
    receiver adjacent adjacentIdentity
  have identity : leading - adjacentInput = (leading - (coarserInput + adjacentInput)) + coarserInput := by abel
  change ‖leading - adjacentInput‖ ≤ _
  rw [identity]
  exact (norm_add_le _ _).trans ((add_le_add remainderBound coarserBound).trans_eq (add_comm _ _))

end EulerNonuniqueness.Paper
