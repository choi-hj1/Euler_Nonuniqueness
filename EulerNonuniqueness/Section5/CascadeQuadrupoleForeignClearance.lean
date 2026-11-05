import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment
import EulerNonuniqueness.Section6.PaperExternalStaticData

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

private theorem quadrupole_average_alignment {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (receiver source : Fin count) (ideal : ℂ) (bound : ℝ)
    (actual : ∀ patch, ‖(patchCentroid motion time receiver patch - quadrupoleCenter motion time source) - ideal‖ ≤ bound) :
    ‖(quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) - ideal‖ ≤ bound := by
  have identity : (quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) - ideal =
      (∑ patch : Fin 4, ((patchCentroid motion time receiver patch - quadrupoleCenter motion time source) - ideal)) / 4 := by
    simp only [quadrupoleCenter, Fin.sum_univ_four]
    ring
  rw [identity, norm_div]
  have summed := (norm_sum_le Finset.univ
    (fun patch : Fin 4 => (patchCentroid motion time receiver patch - quadrupoleCenter motion time source) - ideal)).trans
      (Finset.sum_le_sum (fun patch _ => actual patch))
  norm_num at summed ⊢
  linarith

theorem Scales.eventually_cascade_quadrupole_foreign_clearance (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
      let second := prepared.trajectory.movingFamily.patchMotion
      (∀ source ∈ Finset.univ.erase receiver, ∀ patch position, position ∈ first.domain time source patch →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter first time receiver - position‖) ∧
      (∀ source ∈ Finset.univ.erase receiver, ∀ patch position, position ∈ second.domain time source patch →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter second time receiver - position‖) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have radiusSmall (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have first : changed.radius (source.val + 1) ≤ changed.length (source.val + 1) := by
      simpa only [one_mul] using (radii (source.val + 1)).le
    exact first.trans (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (source.val + 1)).le)
  have domainGap (motion : PatchMotion count)
      (actualAlignment : ∀ source, receiver ≠ source → ∀ patch,
        ‖(patchCentroid motion time receiver patch - quadrupoleCenter motion time source) -
          ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))‖ ≤
          3 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 16)
      (extent : ∀ source, receiver ≠ source → ∀ patch,
        ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤ changed.location (source.val + 1) / 100)
      (domains : ∀ source patch position, position ∈ motion.domain time source patch →
        ‖position - patchCentroid motion time source patch‖ ≤ 2 * changed.radius (source.val + 1)) :
      ∀ source ∈ Finset.univ.erase receiver, ∀ patch position, position ∈ motion.domain time source patch →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter motion time receiver - position‖ := by
    intro source member patch position inDomain
    have different : receiver ≠ source := ((Finset.mem_erase.mp member).1).symm
    have differentIndices : receiver.val + 1 ≠ source.val + 1 :=
      fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    have locations := changed.location_sum_le_three_distance differentIndices
    have receiverPositive := changed.location_pos (receiver.val + 1)
    have sourcePositive := changed.location_pos (source.val + 1)
    have centerAlignment := quadrupole_average_alignment motion time receiver source _ _ (actualAlignment source different)
    have normIdeal : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ =
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have centerTriangle := norm_sub_le_norm_sub_add_norm_sub
      ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))
      (quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) 0
    simp only [sub_zero, normIdeal] at centerTriangle
    have reverseNorm := norm_sub_rev
      ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))
      (quadrupoleCenter motion time receiver - quadrupoleCenter motion time source)
    rw [reverseNorm] at centerTriangle
    have sourceTriangle := norm_sub_le_norm_sub_add_norm_sub position
      (patchCentroid motion time source patch) (quadrupoleCenter motion time source)
    have receiverTriangle := norm_sub_le_norm_sub_add_norm_sub
      (quadrupoleCenter motion time receiver) position (quadrupoleCenter motion time source)
    linarith [domains source patch position inDomain, extent source different patch, radiusSmall source]
  constructor
  · exact domainGap first
      (fun source different patch => (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1)
      (fun source different patch => (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.2.1 patch)
      (fun source patch position member => by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using
          prepared.referenceWitness.trajectory.domain_subset_centroid_ball changed prepared.referenceWitness.radiusIdentity
            (fun _ => rfl) globalInside source patch member)
  · exact domainGap second
      (fun source different patch => (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).2.1)
      (fun source different patch => (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.2.2 patch)
      (fun source patch position member => by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using
          prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity
            (fun _ => rfl) globalInside source patch member)

end EulerNonuniqueness.Paper

