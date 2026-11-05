import EulerNonuniqueness.Section5.CascadePrehitMatchingAccuracy
import EulerNonuniqueness.Section5.CascadeOrbitIncomingMatching

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_actual_incoming_shape_endpoint (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (incomingTime : ℝ)
    {scaleRoot boundaryConstant accuracy : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) (accuracyPositive : 0 < accuracy) :
    ∃ shapeTolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    |unstableShape prepared.trajectory.movingFamily.patchMotion finish index - orbitUnstableShape orbit incomingTime| +
      |stableShape prepared.trajectory.movingFamily.patchMotion finish index - orbitStableShape orbit incomingTime| < shapeTolerance →
    ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
      ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
        index finish rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < accuracy := by
  obtain ⟨tolerance, tolerancePositive, matching⟩ := normalizedSeparatingOrbit_exists_incoming_shape_matching
    orbit normalized incomingTime accuracyPositive
  refine ⟨tolerance, tolerancePositive, ?_⟩
  filter_upwards [scales.eventually_material_prehit_matching_accuracy amplitudePositive ratioBound alphaPositive
    rootPositive boundaryNonnegative (lt_min tolerancePositive (by norm_num : (0 : ℝ) < 1 / 2))]
    with frequency quantitative
  intro sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall shapeClose
  have data := quantitative prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound
    radialSmall finish ⟨finishNonnegative, le_rfl⟩
  have diagonalClose := data.1.trans_le (min_le_left tolerance (1 / 2))
  have neutralClose := data.2.trans_le (min_le_left tolerance (1 / 2))
  have halfBound := data.1.trans_le (min_le_right tolerance (1 / 2))
  have positiveRatio : 0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion finish index /
      ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 := by
    have lower := (abs_lt.mp halfBound).1
    linarith only [lower]
  have positiveDifference : 0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion finish index := by
    have multiplied := (lt_div_iff₀ (sq_pos_of_pos
      (({scales with frequency := frequency} : Scales).length_pos (index.val + 1)))).mp positiveRatio
    simpa only [zero_mul] using multiplied
  exact matching {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion finish index
    positiveDifference diagonalClose shapeClose neutralClose

end EulerNonuniqueness.Paper
