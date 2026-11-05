import EulerNonuniqueness.Section5.CascadeUniformMatchedPassageCentroidExtent
import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_matched_passage_domain_extent_all_incoming
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (outgoingTime : ℝ) :
    ∃ extent ≥ (4 : ℝ), ∀ incomingTime : ℝ, incomingTime < outgoingTime →
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 8 → ∃ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ sectionTime : ℝ, ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ start ∈ Icc 0 path.stop,
    (∀ time ∈ Icc 0 start, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ rotation : ℂ, ‖rotation‖ = 1 →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance →
    ∀ time ∈ Icc 0 (min path.stop (start + (outgoingTime - incomingTime) /
        ({scales with frequency := frequency} : Scales).omega (index.val + 1))), ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
          extent * ({scales with frequency := frequency} : Scales).length (index.val + 1) ∧
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤
          extent * ({scales with frequency := frequency} : Scales).length (index.val + 1) ∧
      prepared.trajectory.movingFamily.patchMotion.domain time index patch ⊆
        closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
          (extent * ({scales with frequency := frequency} : Scales).length (index.val + 1)) ∧
      prepared.referenceWitness.trajectory.movingFamily.patchMotion.domain time index patch ⊆
        closedBall (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index)
          (extent * ({scales with frequency := frequency} : Scales).length (index.val + 1)) := by
  obtain ⟨referenceBound, referenceTwo, bounded⟩ :=
    normalizedSeparatingOrbit_past_configuration_bound orbit normalized outgoingTime
  let centroidExtent := referenceBound + 1
  let extent := referenceBound + 2
  have extentFour : 4 ≤ extent := by dsimp only [extent]; linarith only [referenceTwo]
  have centroidThree : 3 ≤ centroidExtent := by dsimp only [centroidExtent]; linarith only [referenceTwo]
  have extentIdentity : centroidExtent + 1 = extent := by dsimp only [centroidExtent, extent]; ring
  refine ⟨extent, extentFour, ?_⟩
  intro incomingTime timeOrder factor factorPositive factorSmall
  let horizon := outgoingTime - incomingTime
  have horizonPositive : 0 < horizon := sub_pos.mpr timeOrder
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨tolerance, tolerancePositive, shadowing⟩ :=
    exists_universal_material_paper_label_passage_shadowing orbit normalized incomingTime horizon horizonPositive
      1 (by norm_num) factorPositive factorOne
  refine ⟨tolerance, tolerancePositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootPositive boundaryNonnegative
  filter_upwards [shadowing scales amplitudePositive ratioBound alphaPositive sectionTime rootPositive boundaryNonnegative,
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      thresholdSmall referenceNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with frequency shadowEstimate prehit mechanical geometry frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal start startInside radialSmall rotation rotationNorm initial
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have centroidScaled : 3 * length ≤ centroidExtent * length :=
    mul_le_mul_of_nonneg_right centroidThree lengthPositive.le
  have extentScaled : centroidExtent * length ≤ extent * length := by
    rw [← extentIdentity]
    nlinarith only [lengthPositive]
  have radiusSmall : 2 * changed.radius (index.val + 1) ≤ length := by
    have radiusBound := (geometry (index.val + 1)).2.1
    change changed.radius (index.val + 1) ≤ 1 * length / 1000 at radiusBound
    linarith only [radiusBound, lengthPositive]
  have paperReferenceBound (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖centrallySymmetricFourPoint (orbit.positive (elapsed + incomingTime))
        (orbit.negative (elapsed + incomingTime))‖ ≤ referenceBound := by
    have identity := relabelNegativePoints_norm (centrallySymmetricFourPoint
      (orbit.positive (elapsed + incomingTime)) (-orbit.negative (elapsed + incomingTime)))
    simp only [relabelNegativePoints_central, neg_neg] at identity
    have beforeOutgoing : elapsed + incomingTime ≤ outgoingTime := by
      dsimp only [horizon] at inside
      linarith only [inside.2]
    exact identity.trans_le (bounded (elapsed + incomingTime) beforeOutgoing)
  intro time inside patch
  have actualInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans (min_le_left _ _)⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [actualInside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, actualInside.2.trans (path.stopBound.trans (by norm_num))⟩
  have referenceControl : ‖patchCentroid reference time index patch - quadrupoleCenter reference time index‖ ≤
      centroidExtent * length := ((mechanical _ prepared.referenceWitness.evolution prepared.referenceWitness.coarse
        time referenceInside index).1.centroidsBounded patch).trans centroidScaled
  have actualControl : ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤
      centroidExtent * length := by
    by_cases beforeEntry : time ≤ start
    · exact (prehit prepared path factorSmall index nonterminal start startInside.1 startInside.2 radialSmall
        time ⟨inside.1, beforeEntry⟩ patch).1.trans centroidScaled
    have afterEntry : start < time := lt_of_not_ge beforeEntry
    let elapsed := omega * (time - start)
    have elapsedPositive : 0 < elapsed := mul_pos omegaPositive (sub_pos.mpr afterEntry)
    have physicalIdentity : start + elapsed / omega = time := by dsimp only [elapsed]; field_simp
    have elapsedBound : elapsed ≤ horizon := by
      have timeBound : time ≤ start + horizon / omega := inside.2.trans (min_le_right _ _)
      have divided : time - start ≤ horizon / omega := by linarith only [timeBound]
      have multiplied := (le_div_iff₀ omegaPositive).mp divided
      dsimp only [elapsed]
      nlinarith only [multiplied]
    have windowInside (current : ℝ) (member : current ∈ Icc 0 elapsed) :
        start + current / omega ∈ Icc 0 path.stop := by
      refine ⟨add_nonneg startInside.1 (div_nonneg member.1 omegaPositive.le), ?_⟩
      have upper := add_le_add_left (div_le_div_of_nonneg_right member.2 omegaPositive.le) start
      rw [physicalIdentity] at upper
      exact upper.trans actualInside.2
    have close := shadowEstimate count phase dipoleAngle prepared path index start elapsed elapsedPositive elapsedBound
      rotation rotationNorm windowInside initial elapsed ⟨elapsedPositive.le, le_rfl⟩
    have referenceControl := paperReferenceBound elapsed ⟨elapsedPositive.le, elapsedBound⟩
    have triangle := norm_add_le
      (cascadeNormalizedPointPositions changed motion index start rotation elapsed -
        centrallySymmetricFourPoint (orbit.positive (elapsed + incomingTime)) (orbit.negative (elapsed + incomingTime)))
      (centrallySymmetricFourPoint (orbit.positive (elapsed + incomingTime)) (orbit.negative (elapsed + incomingTime)))
    rw [sub_add_cancel] at triangle
    have normalizedBound : ‖cascadeNormalizedPointPositions changed motion index start rotation elapsed‖ ≤ centroidExtent := by
      dsimp only [centroidExtent]
      linarith only [triangle, close, referenceControl]
    let positions : FourPointConfiguration := fun label => patchCentroid motion time index label
    have scaling := normalized_configuration_norm (fourPointCenterProjection positions) lengthPositive rotationNorm
    have normalizedIdentity : cascadeNormalizedPointPositions changed motion index start rotation elapsed =
        fun label => ((length : ℂ) * rotation)⁻¹ * fourPointCenterProjection positions label := by
      funext label
      dsimp only [cascadeNormalizedPointPositions]
      rw [physicalIdentity]
    rw [normalizedIdentity, scaling] at normalizedBound
    have positionBound : ‖fourPointCenterProjection positions‖ ≤ centroidExtent * length :=
      (div_le_iff₀ lengthPositive).mp normalizedBound
    exact (norm_le_pi_norm (fourPointCenterProjection positions) patch).trans positionBound
  refine ⟨actualControl.trans extentScaled, referenceControl.trans extentScaled, ?_, ?_⟩
  · intro position member
    have domainBound := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl)
      globalInside index patch member
    rw [mem_closedBall, dist_eq_norm] at domainBound ⊢
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion time index patch)
      (quadrupoleCenter motion time index)
    rw [← extentIdentity]
    nlinarith only [triangle, domainBound, actualControl, radiusSmall]
  · intro position member
    have domainBound := prepared.referenceWitness.trajectory.domain_subset_centroid_ball changed
      prepared.referenceWitness.radiusIdentity (fun _ => rfl) globalInside index patch member
    rw [mem_closedBall, dist_eq_norm] at domainBound ⊢
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid reference time index patch)
      (quadrupoleCenter reference time index)
    rw [← extentIdentity]
    nlinarith only [triangle, domainBound, referenceControl, radiusSmall]

end EulerNonuniqueness.Paper
