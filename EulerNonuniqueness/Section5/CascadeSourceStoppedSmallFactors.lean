import EulerNonuniqueness.Section5.CascadeSourcePreparedSmallFactors
import EulerNonuniqueness.Section5.CascadeParameterPrerequisites
import EulerNonuniqueness.Section5.CascadeProof
import EulerNonuniqueness.Section5.CascadeInternallyStoppedExistence

noncomputable section

open Filter

namespace EulerNonuniqueness.Paper

theorem exists_uniform_source_stopped_cascade_parameters_for_small_factors
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    {sectionTime : ℝ} (sectionTimePositive : 0 < sectionTime) :
    ∃ shapeRadius > (0 : ℝ), ∃ factorMax > (0 : ℝ), factorMax ≤ 1 / 100 ∧
    ∀ factor : ℝ, 0 < factor → factor ≤ factorMax →
    ∀ requestedCap : ℝ, 0 < requestedCap →
    ∃ monitor > (0 : ℝ), ∃ boundaryConstant ≥ (1 : ℝ),
    ∀ {alpha ratio : ℝ}, 0 < alpha → alpha < 1 → 2 < ratio →
    ∀ thresholdUpper : ℝ, 0 < thresholdUpper →
    ∀ {tolerance timingConstant : ℝ}, 0 < tolerance → tolerance < 1 / 8 → 0 < timingConstant →
    ∃ threshold > (0 : ℝ), threshold < thresholdUpper ∧ threshold < 1 / 8 ∧
    ∃ rootMin ≥ (8 : ℝ),
    ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
    ∃ referenceConstant > (0 : ℝ), referenceConstant ≤ scaleRoot ^ 3 ∧
    ∀ᶠ frequency : ℝ in atTop,
      CascadeParameterPrerequisites ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit
        sectionTime threshold tolerance timingConstant ∧
      ∀ count : ℕ, 2 ≤ count → ∃ phase dipoleAngle : ℕ → ℝ,
        PrescribedCascadePhases ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime count phase dipoleAngle ∧
        ∃ prepared : CascadeSourcePreparedPair requestedCap ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩
          orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius
          factor monitor boundaryConstant count,
          Nonempty (CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair) := by
  obtain ⟨shapeRadius, shapePositive, factorMax, factorMaxPositive, factorMaxSmall, preparations⟩ :=
    exists_uniform_source_prepared_cascade_pairs_for_small_factors orbit normalized sectionTime
  refine ⟨shapeRadius, shapePositive, factorMax, factorMaxPositive, factorMaxSmall, ?_⟩
  intro factor factorPositive factorBound requestedCap requestedPositive
  obtain ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, parameters⟩ :=
    preparations factor factorPositive factorBound requestedCap requestedPositive
  refine ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, ?_⟩
  intro alpha ratio alphaPositive alphaSmall ratioLarge thresholdUpper thresholdUpperPositive
    tolerance timingConstant tolerancePositive toleranceSmall timingPositive
  obtain ⟨threshold, thresholdPositive, thresholdUpperBound, thresholdSmall, rootMin, rootEight, constructions⟩ :=
    parameters alphaPositive alphaSmall ratioLarge thresholdUpper thresholdUpperPositive
  refine ⟨threshold, thresholdPositive, thresholdUpperBound, thresholdSmall, rootMin, rootEight, ?_⟩
  intro scaleRoot rootLarge
  obtain ⟨referenceConstant, referencePositive, referenceAmplitude, pairs⟩ := constructions scaleRoot rootLarge
  refine ⟨referenceConstant, referencePositive, referenceAmplitude, ?_⟩
  let base : Scales := ⟨alpha, scaleRoot ^ 3, ratio, 0⟩
  have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scaleRoot ^ 3 := by positivity
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have factorOne : factor ≤ 1 := factorBound.trans (factorMaxSmall.trans (by norm_num))
  have thresholdHalf : threshold ≤ 1 / 2 := thresholdSmall.le.trans (by norm_num)
  have prerequisites := base.eventually_cascadeParameterPrerequisites orbit alphaPositive alphaSmall
    amplitudePositive ratioLarge normalized sectionTimePositive thresholdPositive thresholdSmall
    tolerancePositive toleranceSmall timingPositive
  have stopped := base.eventually_exists_internally_stopped_cascade amplitudePositive ratioLarge.le alphaPositive
    orbit sectionTime (factor := factor) (threshold := threshold) (scaleRoot := scaleRoot)
    (boundaryConstant := boundaryConstant) factorPositive factorOne thresholdHalf rootOne boundaryOne
  filter_upwards [pairs, prerequisites, stopped] with frequency actual prerequisite stops
  refine ⟨prerequisite, ?_⟩
  intro count countLarge
  obtain ⟨phase, dipoleAngle, prescribed⟩ := prescribedCascadePhases_exist
    ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime count
  obtain ⟨prepared⟩ := actual count countLarge phase dipoleAngle
  exact ⟨phase, dipoleAngle, prescribed, prepared,
    stops count (by omega) phase dipoleAngle prepared.toCascadeMaterialPreparedPair⟩

end EulerNonuniqueness.Paper
