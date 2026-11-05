import EulerNonuniqueness.Section5.CascadeSourcePreparedConstruction
import EulerNonuniqueness.Section5.CascadeParameterPrerequisites
import EulerNonuniqueness.Section5.CascadeProof
import EulerNonuniqueness.Section5.CascadeInternallyStoppedExistence

noncomputable section

open Filter

namespace EulerNonuniqueness.Paper

theorem exists_uniform_source_stopped_cascade_parameters
    (requestedCap : ℝ) (requestedPositive : 0 < requestedCap)
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (alphaSmall : alpha < 1) (ratioLarge : 2 < ratio)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    {sectionTime tolerance timingConstant : ℝ} (sectionTimePositive : 0 < sectionTime)
    (tolerancePositive : 0 < tolerance) (toleranceSmall : tolerance < 1 / 8)
    (timingPositive : 0 < timingConstant) :
    ∃ threshold > (0 : ℝ), threshold < 1 / 8 ∧
    ∃ shapeRadius > (0 : ℝ), ∃ factor > (0 : ℝ), factor ≤ 1 / 8 ∧
    ∃ monitor > (0 : ℝ), ∃ boundaryConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot → ∃ referenceConstant > (0 : ℝ), referenceConstant ≤ scaleRoot ^ 3 ∧
    ∀ᶠ frequency : ℝ in atTop,
      CascadeParameterPrerequisites ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit
        sectionTime threshold tolerance timingConstant ∧
      ∀ count : ℕ, 2 ≤ count → ∃ phase dipoleAngle : ℕ → ℝ,
        PrescribedCascadePhases ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime count phase dipoleAngle ∧
        ∃ prepared : CascadeSourcePreparedPair requestedCap ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime phase dipoleAngle
          threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
          Nonempty (CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair) := by
  obtain ⟨threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive,
    factor, factorPositive, factorSmall, monitor, monitorPositive, boundaryConstant, boundaryOne,
    rootMin, rootEight, constructions⟩ :=
    exists_uniform_source_prepared_cascade_pairs requestedCap requestedPositive alphaPositive alphaSmall ratioLarge orbit normalized sectionTime
  refine ⟨threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive, factor, factorPositive,
    factorSmall, monitor, monitorPositive, boundaryConstant, boundaryOne, rootMin, rootEight, ?_⟩
  intro scaleRoot rootLarge
  obtain ⟨referenceConstant, referencePositive, referenceAmplitudeBound, prepared⟩ := constructions scaleRoot rootLarge
  refine ⟨referenceConstant, referencePositive, referenceAmplitudeBound, ?_⟩
  let base : Scales := ⟨alpha, scaleRoot ^ 3, ratio, 0⟩
  have rootPositive : 0 < scaleRoot := by linarith [rootEight.trans rootLarge]
  have prerequisites := base.eventually_cascadeParameterPrerequisites orbit alphaPositive alphaSmall
    (show 0 < scaleRoot ^ 3 by positivity) ratioLarge normalized sectionTimePositive thresholdPositive
    thresholdSmall tolerancePositive toleranceSmall timingPositive
  have stopped := base.eventually_exists_internally_stopped_cascade (show 0 < scaleRoot ^ 3 by positivity)
    ratioLarge.le alphaPositive orbit sectionTime (factor := factor) (threshold := threshold)
    (scaleRoot := scaleRoot) (boundaryConstant := boundaryConstant) factorPositive (by linarith) (by linarith)
    (by linarith [rootEight.trans rootLarge]) boundaryOne
  filter_upwards [prepared, prerequisites, stopped] with frequency actual prerequisites stops
  refine ⟨prerequisites, ?_⟩
  intro count countLarge
  obtain ⟨phase, dipoleAngle, prescribed⟩ := prescribedCascadePhases_exist
    ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime count
  obtain ⟨pair⟩ := actual count countLarge phase dipoleAngle
  exact ⟨phase, dipoleAngle, prescribed, pair, stops count (by omega) phase dipoleAngle pair.toCascadeMaterialPreparedPair⟩

end EulerNonuniqueness.Paper




