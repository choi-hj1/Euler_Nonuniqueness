import EulerNonuniqueness.Section6.SourcePacketAnchorVectorDrift

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_source_packet_receiver_displacement_freezing (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant receiverRadiusFactor tolerance : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 2) (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (receiverRadiusPositive : 0 < receiverRadiusFactor) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
    ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
    ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver‖ ≤
        receiverRadiusFactor * ({scales with frequency := frequency} : Scales).length (receiver.val + 1) →
    ‖(patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source) -
      (({scales with frequency := frequency} : Scales).location (receiver.val + 1) -
        (({scales with frequency := frequency} : Scales).location (source.val + 1) : ℂ))‖ ≤
      tolerance * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
  filter_upwards [scales.eventually_source_packet_anchor_vector_drift amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall thresholdSmall rootOne boundaryOne (tolerance := 4 * tolerance) (by positivity),
    scales.eventually_length_lt_location ratioBound alphaPositive
      (show (0 : ℝ) < tolerance / (6 * receiverRadiusFactor) by positivity)] with frequency drift lengths
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path time inside receiver source different patch ownRadius
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let gap := |scales.location (receiver.val + 1) - scales.location (source.val + 1)|
  have actual := drift count phase dipoleAngle prepared path time inside receiver source
  have locations := changed.location_sum_le_three_distance (show receiver.val + 1 ≠ source.val + 1 from
    fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have receiverLocation : changed.location (receiver.val + 1) ≤ 3 * gap := by
    change changed.location (receiver.val + 1) + changed.location (source.val + 1) ≤ 3 * gap at locations
    linarith [changed.location_pos (source.val + 1)]
  have lengthSmall : receiverRadiusFactor * changed.length (receiver.val + 1) ≤ tolerance * gap / 2 := by
    have first := mul_le_mul_of_nonneg_left (lengths (receiver.val + 1)).le receiverRadiusPositive.le
    have second := mul_le_mul_of_nonneg_left receiverLocation (show 0 ≤ tolerance / 6 by positivity)
    have normalized : receiverRadiusFactor * changed.length (receiver.val + 1) ≤
        (tolerance / 6) * changed.location (receiver.val + 1) := by
      convert first using 1 <;> dsimp only [changed, Scales.location] <;>
        field_simp [receiverRadiusPositive.ne'] <;> ring
    exact normalized.trans (by convert second using 1 <;> ring)
  have identity : (patchCentroid motion time receiver patch - quadrupoleCenter motion time source) -
      ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)) =
      (patchCentroid motion time receiver patch - quadrupoleCenter motion time receiver) +
        ((quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) -
          ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))) := by abel
  rw [identity]
  have triangle := norm_add_le
    (patchCentroid motion time receiver patch - quadrupoleCenter motion time receiver)
    ((quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) -
      ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)))
  have bound := triangle.trans (add_le_add (ownRadius.trans lengthSmall) actual)
  convert bound using 1 <;> dsimp only [changed, gap, Scales.location] <;> ring

end EulerNonuniqueness.Paper
