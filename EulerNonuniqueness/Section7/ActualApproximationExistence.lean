import EulerNonuniqueness.Section6.SourcePacketFirstSectionSelection
import EulerNonuniqueness.Section5.CascadeSourceStoppedSmallFactors
import EulerNonuniqueness.Section5.CascadeUniformStageProducers
import EulerNonuniqueness.Section7.PhysicalStageFamilyApproximation
import EulerNonuniqueness.Section1.CascadeSourceRateRatioChoice

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6 EulerNonuniqueness.Section2
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

/-- Actual finite cascades, with every stage constructed by finite descent, supply the approximation data. -/
theorem exists_actual_approximation_data : Nonempty ApproximationData := by
  classical
  let eta : ℝ := 1 / 1000
  have etaPositive : 0 < eta := by norm_num [eta]
  have etaSmall : eta ≤ 1 / 1000 := le_rfl
  let modelTolerance := min (((eta / 1000) / 4) / 2) (1 / 8)
  have modelPositive : 0 < modelTolerance := by dsimp only [modelTolerance]; positivity
  obtain ⟨timeShift, rotationPhase, modelDipoleAngle, offset, normalized, modelFactor, modelFactorPositive,
    modelFactorSmall, modelSeparated, sections⟩ := normalizedSeparatingCandidate_exists_with_signed_first_sections
  let orbit := separatingCandidate timeShift rotationPhase modelDipoleAngle offset
  let modelDerivative := fun time : ℝ =>
    separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))
  obtain ⟨sectionTime, sectionOne, initialError, errorPositive, errorSmall, radiusBound, transverse,
    earlierMargin, separationClose, outgoing, numericBudget⟩ := sections modelTolerance modelPositive 2048
  have sectionPositive : 0 < sectionTime := zero_lt_one.trans sectionOne
  have radiusLarge : 2048 ≤ separationRadius orbit sectionTime := (le_max_left _ _).trans radiusBound
  obtain ⟨thresholdMax, thresholdMaxPositive, thresholdMaxEighth, rawCap, rawCapPositive, stageFactors⟩ :=
    exists_uniform_actual_stage_producers etaPositive etaSmall orbit normalized sectionTime initialError modelDerivative
      sectionPositive errorPositive errorSmall radiusLarge transverse earlierMargin separationClose outgoing numericBudget
  obtain ⟨shapeRadius, shapePositive, factorMax, factorMaxPositive, factorMaxSmall, preparations⟩ :=
    exists_uniform_source_stopped_cascade_parameters_for_small_factors orbit normalized sectionPositive
  let factor := min factorMax modelFactor / 2
  have factorPositive : 0 < factor := half_pos (lt_min factorMaxPositive modelFactorPositive)
  have factorHalf : factor ≤ min factorMax modelFactor :=
    (half_lt_self (lt_min factorMaxPositive modelFactorPositive)).le
  have factorBound : factor ≤ factorMax := factorHalf.trans (min_le_left _ _)
  have factorModel : factor ≤ modelFactor := factorHalf.trans (min_le_right _ _)
  have factorSmall : factor ≤ 1 / 100 := factorBound.trans factorMaxSmall
  have referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖ := by
    intro time target source different
    exact (mul_le_mul_of_nonneg_left factorModel (by norm_num : (0 : ℝ) ≤ 2)).trans
      (modelSeparated time target source different)
  obtain ⟨extent, extentFour, stageRoot, stageRootEight, endpointMax, endpointMaxPositive, endpointMaxOne,
    stageEndpoints⟩ := stageFactors factor factorPositive factorSmall referenceSeparated
  obtain ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, constructorParameters⟩ :=
    preparations factor factorPositive factorBound rawCap rawCapPositive
  let endpoint := endpointMax / 2
  have endpointPositive : 0 < endpoint := half_pos endpointMaxPositive
  have endpointBound : endpoint ≤ endpointMax := (half_lt_self endpointMaxPositive).le
  obtain ⟨incomingTime, sectionAfter, historyMagnitude, historyNonnegative, stageAccuracy⟩ :=
    (stageEndpoints endpoint endpointPositive endpointBound).exists
  have incomingBefore : incomingTime < sectionTime := by linarith only [sectionAfter]
  obtain ⟨stopTolerance, stopPositive, approximationParameters⟩ :=
    exists_universal_approximationData_of_physical_stage_families orbit normalized sectionTime incomingTime incomingBefore
      factorPositive (factorSmall.trans (by norm_num)) errorPositive errorSmall referenceSeparated radiusLarge separationClose outgoing
  obtain ⟨matchingMax, matchingMaxPositive, matchingMaxStop, stageMatching⟩ := stageAccuracy stopTolerance stopPositive
  let matchingAccuracy := matchingMax / 2
  have matchingPositive : 0 < matchingAccuracy := half_pos matchingMaxPositive
  have matchingBound : matchingAccuracy ≤ matchingMax := (half_lt_self matchingMaxPositive).le
  have matchingStop : matchingAccuracy ≤ stopTolerance := matchingBound.trans matchingMaxStop
  obtain ⟨stageRatio, stageRatioLarge, stageScales⟩ := stageMatching matchingAccuracy matchingPositive matchingBound
  have alphaPositive : (0 : ℝ) < 1 / 2 := by norm_num
  have alphaSmall : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨ratio, ratioLower, ratioChoices⟩ := exists_cascade_source_rate_ratio_threshold
    alphaPositive alphaSmall (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1 / 8)
      (max 3 stageRatio) ((2 * Real.sqrt 2 + 1) * 8)
  have ratioThree : 3 ≤ ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLower)
  have ratioLarge : 2 < ratio := by linarith only [ratioThree]
  have stageRatioBound : stageRatio ≤ ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLower)
  obtain ⟨ratioPower, ratioSeparation, controlledSeparation⟩ := ratioChoices ratio le_rfl
  obtain ⟨threshold, thresholdPositive, thresholdBound, thresholdSmall, constructorRoot,
    constructorRootEight, constructions⟩ := constructorParameters alphaPositive alphaSmall ratioLarge
      thresholdMax thresholdMaxPositive (tolerance := 1 / 16) (timingConstant := 1)
      (by norm_num) (by norm_num) (by norm_num)
  let scaleRoot := max stageRoot constructorRoot
  have stageRootBound : stageRoot ≤ scaleRoot := le_max_left _ _
  have constructorRootBound : constructorRoot ≤ scaleRoot := le_max_right _ _
  have rootEight : 8 ≤ scaleRoot := stageRootEight.trans stageRootBound
  have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) rootEight
  obtain ⟨referenceConstant, referencePositive, referenceAmplitude, actual⟩ := constructions scaleRoot constructorRootBound
  let base : Scales := ⟨1 / 2, scaleRoot ^ 3, ratio, 0⟩
  have amplitudePositive : 0 < base.amplitude := by change 0 < scaleRoot ^ 3; positivity
  have stageEvent := stageScales base scaleRoot stageRootBound rfl stageRatioBound alphaPositive alphaSmall ratioPower
    referenceConstant referencePositive.le referenceAmplitude threshold thresholdBound.le boundaryConstant boundaryOne
    (by simpa only [base, mul_comm] using controlledSeparation)
  have approximationEvent := approximationParameters base amplitudePositive ratioLarge.le alphaPositive
    thresholdSmall.le rootPositive (by linarith only [boundaryOne]) referencePositive.le
  obtain ⟨frequency, actualAt, stageAt, approximationAt⟩ := (actual.and (stageEvent.and approximationEvent)).exists
  have families : ∀ family : ℕ, ∃ phase dipoleAngle : ℕ → ℝ,
      ∃ prepared : CascadeSourcePreparedPair rawCap {base with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant (family + 2),
      ∃ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∃ records : (index : Fin (family + 2)) → CascadePhysicalStageData prepared path index incomingTime extent historyMagnitude
        (1 / 16) initialError (eta / 100) eta stopTolerance,
        ∀ index : Fin (family + 2), (records index).entry < 1 / 2 := by
    intro family
    obtain ⟨phase, dipoleAngle, prescribed, prepared, pathExists⟩ := actualAt.2 (family + 2) (by omega)
    obtain ⟨path⟩ := pathExists
    have stage := stageAt (family + 2) (by omega) phase dipoleAngle
    obtain ⟨terminal, terminalZero, producer⟩ := stage.2 prepared path prescribed
    obtain ⟨records, ordered, entriesHalf⟩ := exists_physical_stage_family_of_next_stage_producer (by omega) terminal
      (fun index => (stage.1 index).1) (fun index => (stage.1 index).2.2)
      (fun index => (stage.1 index).2.1) producer
    let enlarged := fun index => (records index).weakenBounds (le_refl extent) (le_refl historyMagnitude)
      (le_refl (eta / 100)) (le_refl eta) matchingStop
    refine ⟨phase, dipoleAngle, prepared, path, enlarged, ?_⟩
    intro index
    exact entriesHalf index
  choose phase dipoleAngle prepared paths records entriesHalf using families
  have truncationsTendsto : Tendsto (fun family : ℕ => family + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    filter_upwards [eventually_ge_atTop bound] with family familyLarge
    omega
  exact approximationAt (fun family : ℕ => family + 1) truncationsTendsto phase dipoleAngle
    (fun _ => shapeRadius) (fun _ => monitor) (fun _ => rawCap) prepared paths
    extent historyMagnitude (1 / 16) (eta / 100) eta records (fun family => (entriesHalf family ⟨0, by omega⟩).le)

end EulerNonuniqueness.Paper
