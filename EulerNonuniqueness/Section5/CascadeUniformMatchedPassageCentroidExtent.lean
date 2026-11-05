import EulerNonuniqueness.Section5.UniversalMaterialPassageShadowing
import EulerNonuniqueness.Section7.ActualIncomingShapeEndpoint
import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section6.CenteredPointNormScaling

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem normalizedSeparatingOrbit_past_configuration_bound
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (outgoingTime : ℝ) :
    ∃ bound ≥ (2 : ℝ), ∀ time ≤ outgoingTime,
      ‖centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time)‖ ≤ bound := by
  have rhombusHalf : EulerNonuniqueness.Section2.rhombusRatio < (1 / 2 : ℝ) := by
    unfold EulerNonuniqueness.Section2.rhombusRatio
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have ratioIncoming := normalized.2.2.2.1
  have ratioSmall := ratioIncoming.eventually (eventually_lt_nhds rhombusHalf)
  obtain ⟨cutoff, tail⟩ := eventually_atBot.mp ratioSmall
  let lower := min cutoff outgoingTime
  have tailBound (time : ℝ) (early : time ≤ lower) :
      ‖centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time)‖ ≤ (2 : ℝ) := by
    have impulse := (normalized.2.1 time).1
    have positiveSquare : 0 < ‖orbit.positive time‖ ^ 2 := by
      nlinarith only [impulse, sq_nonneg ‖orbit.negative time‖]
    have ratioBound := (tail time (early.trans (min_le_left _ _))).le
    have negativeSquare := (div_le_iff₀ positiveSquare).mp ratioBound
    have positiveBound : ‖orbit.positive time‖ ≤ (2 : ℝ) := by
      nlinarith only [impulse, negativeSquare, norm_nonneg (orbit.positive time)]
    have negativeBound : ‖orbit.negative time‖ ≤ (2 : ℝ) := by
      nlinarith only [impulse, negativeSquare, norm_nonneg (orbit.negative time)]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro label
    fin_cases label
    · simpa [centrallySymmetricFourPoint] using positiveBound
    · simpa [centrallySymmetricFourPoint] using positiveBound
    · simpa [centrallySymmetricFourPoint] using negativeBound
    · simpa [centrallySymmetricFourPoint] using negativeBound
  have regular : ContinuousOn (fun time => centrallySymmetricFourPoint
      (orbit.positive time) (-orbit.negative time)) (Icc lower outgoingTime) := by
    intro time _
    exact (normalizedSeparatingOrbit_full_point_equation orbit normalized time).1.continuousAt.continuousWithinAt
  obtain ⟨compactBound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn regular
  refine ⟨max 2 compactBound, le_max_left _ _, ?_⟩
  intro time beforeOutgoing
  by_cases early : time ≤ lower
  · exact (tailBound time early).trans (le_max_left _ _)
  · exact (bounded time ⟨(lt_of_not_ge early).le, beforeOutgoing⟩).trans (le_max_right _ _)

theorem exists_uniform_actual_matched_passage_centroid_extent_all_incoming
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (outgoingTime : ℝ) :
    ∃ extent ≥ (3 : ℝ), ∀ incomingTime : ℝ, incomingTime < outgoingTime →
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 8 →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ sectionTime : ℝ, ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∃ shapeTolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ start ∈ Icc 0 path.stop,
    (∀ time ∈ Icc 0 start, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    |unstableShape prepared.trajectory.movingFamily.patchMotion start index - orbitUnstableShape orbit incomingTime| +
      |stableShape prepared.trajectory.movingFamily.patchMotion start index - orbitStableShape orbit incomingTime| < shapeTolerance →
    ∀ time ∈ Icc 0 (min path.stop (start + (outgoingTime - incomingTime) /
        ({scales with frequency := frequency} : Scales).omega (index.val + 1))), ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
          extent * ({scales with frequency := frequency} : Scales).length (index.val + 1) ∧
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤
          extent * ({scales with frequency := frequency} : Scales).length (index.val + 1) := by
  obtain ⟨referenceBound, referenceTwo, bounded⟩ :=
    normalizedSeparatingOrbit_past_configuration_bound orbit normalized outgoingTime
  let extent := referenceBound + 1
  have extentThree : 3 ≤ extent := by dsimp only [extent]; linarith only [referenceTwo]
  refine ⟨extent, extentThree, ?_⟩
  intro incomingTime timeOrder
  let horizon := outgoingTime - incomingTime
  have horizonPositive : 0 < horizon := sub_pos.mpr timeOrder
  have referenceExtent : referenceBound + 1 ≤ extent := le_rfl
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
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨tolerance, tolerancePositive, shadowing⟩ :=
    exists_universal_material_paper_label_passage_shadowing orbit normalized incomingTime horizon horizonPositive
      1 (by norm_num) factorPositive factorOne
  intro scales amplitudePositive ratioBound alphaPositive sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootPositive boundaryNonnegative
  obtain ⟨shapeTolerance, shapeTolerancePositive, matching⟩ :=
    scales.eventually_actual_incoming_shape_endpoint amplitudePositive ratioBound alphaPositive orbit normalized incomingTime
      rootPositive boundaryNonnegative tolerancePositive
  refine ⟨shapeTolerance, shapeTolerancePositive, ?_⟩
  filter_upwards [shadowing scales amplitudePositive ratioBound alphaPositive sectionTime
      rootPositive boundaryNonnegative,
    matching,
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      thresholdSmall referenceNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency shadowEstimate matchEstimate prehit mechanical frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal start startInside radialSmall shapeClose
  obtain ⟨rotation, rotationNorm, initialClose⟩ := matchEstimate prepared path (thresholdSmall.trans (by norm_num)) factorSmall
    index nonterminal start startInside.1 startInside.2 radialSmall shapeClose
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have threeScaled : 3 * length ≤ extent * length := mul_le_mul_of_nonneg_right extentThree lengthPositive.le
  intro time inside patch
  have actualInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans (min_le_left _ _)⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, actualInside.2.trans (path.stopBound.trans (by norm_num))⟩
  have referenceControl := (mechanical _ prepared.referenceWitness.evolution prepared.referenceWitness.coarse
    time referenceInside index).1.centroidsBounded patch
  refine ⟨?_, referenceControl.trans threeScaled⟩
  by_cases beforeEntry : time ≤ start
  · have actual := prehit prepared path factorSmall index nonterminal start startInside.1 startInside.2 radialSmall
      time ⟨inside.1, beforeEntry⟩ patch
    exact actual.1.trans threeScaled
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
    rotation rotationNorm windowInside initialClose.le elapsed ⟨elapsedPositive.le, le_rfl⟩
  have referenceControl := paperReferenceBound elapsed ⟨elapsedPositive.le, elapsedBound⟩
  have triangle := norm_add_le
    (cascadeNormalizedPointPositions changed motion index start rotation elapsed -
      centrallySymmetricFourPoint (orbit.positive (elapsed + incomingTime)) (orbit.negative (elapsed + incomingTime)))
    (centrallySymmetricFourPoint (orbit.positive (elapsed + incomingTime)) (orbit.negative (elapsed + incomingTime)))
  rw [sub_add_cancel] at triangle
  have normalizedBound : ‖cascadeNormalizedPointPositions changed motion index start rotation elapsed‖ ≤ extent := by
    linarith only [triangle, close, referenceControl, referenceExtent]
  let positions : FourPointConfiguration := fun label => patchCentroid motion time index label
  have scaling := normalized_configuration_norm (fourPointCenterProjection positions) lengthPositive rotationNorm
  have normalizedIdentity : cascadeNormalizedPointPositions changed motion index start rotation elapsed =
      fun label => ((length : ℂ) * rotation)⁻¹ * fourPointCenterProjection positions label := by
    funext label
    dsimp only [cascadeNormalizedPointPositions]
    rw [physicalIdentity]
  rw [normalizedIdentity, scaling] at normalizedBound
  have positionBound : ‖fourPointCenterProjection positions‖ ≤ extent * length :=
    (div_le_iff₀ lengthPositive).mp normalizedBound
  exact (norm_le_pi_norm (fourPointCenterProjection positions) patch).trans positionBound

end EulerNonuniqueness.Paper

