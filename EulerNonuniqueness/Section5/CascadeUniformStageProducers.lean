import EulerNonuniqueness.Section5.CascadeTerminalCalibratedStage
import EulerNonuniqueness.Section5.CascadeCalibratedStage
import EulerNonuniqueness.Section5.CascadePhysicalStageDescent
import EulerNonuniqueness.Section5.CascadePhysicalStageDataCap
import EulerNonuniqueness.Section5.CascadeSeparationContact
import EulerNonuniqueness.Section5.CascadeUniformPredictedTime

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

/-- The exact physical producer used by finite descent, with no chart shared between stages. -/
def CascadeNextStageProducer
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (incomingTime extent magnitude coefficient error phaseTolerance timingTolerance matchingTolerance : ℝ) : Prop :=
  ∀ (index : Fin count) (nonterminal : index.val + 1 < count),
    ∀ prior : ∀ other : Fin count, index.val < other.val →
      CascadePhysicalStageData prepared path other incomingTime extent magnitude coefficient error
        phaseTolerance timingTolerance matchingTolerance,
    (∀ (first second : Fin count) (firstFiner : index.val < first.val) (secondFiner : index.val < second.val),
      first.val < second.val → (prior second secondFiner).entry < (prior first firstFiner).entry) →
    (prior ⟨index.val + 1, nonterminal⟩ (Nat.lt_succ_self index.val)).entry ≤ 1 / 2 →
    ∃ data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance,
      (prior ⟨index.val + 1, nonterminal⟩ (Nat.lt_succ_self index.val)).entry < data.entry

theorem exists_uniform_actual_stage_producers
    {eta : ℝ} (etaPositive : 0 < eta) (etaSmall : eta ≤ 1 / 1000)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime initialError : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionPositive : 0 < sectionTime) (errorPositive : 0 < initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (transverse : ∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
      HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time)
    (earlierMargin : ∀ time ≤ sectionTime - 1,
      separationRadius orbit time ≤ separationRadius orbit sectionTime - 1)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
    (numericBudget : 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
      min ((min (((eta / 1000) / 4) / 2) (1 / 8)) / 4) 1 / 5120) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) →
    ∃ extent ≥ (4 : ℝ), ∃ rootMin ≥ (8 : ℝ), ∃ endpointMax > (0 : ℝ), endpointMax ≤ 1 ∧
    ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax →
    ∀ᶠ incomingTime : ℝ in atBot, incomingTime + 1 < sectionTime ∧
    ∃ historyMagnitude ≥ (0 : ℝ), ∀ stopTolerance > (0 : ℝ),
    ∃ matchingMax > (0 : ℝ), matchingMax ≤ stopTolerance ∧
    ∀ matchingAccuracy : ℝ, 0 < matchingAccuracy → matchingAccuracy ≤ matchingMax →
    ∃ ratioMin ≥ (128 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ boundaryConstant : ℝ, 1 ≤ boundaryConstant →
    ((1 / 16 : ℝ) * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ (count : ℕ) (countLarge : 2 ≤ count), ∀ phase dipoleAngle : ℕ → ℝ,
    let changed : Scales := {scales with frequency := frequency}
    (∀ index : Fin count, 0 < changed.omega (index.val + 1) ∧
      eta / changed.omega (index.val + 1) < 1 / 4 ∧ changed.predictedTime sectionTime count (index.val + 1) < 1 / 4) ∧
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap changed orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    PrescribedCascadePhases changed orbit sectionTime count phase dipoleAngle →
    ∃ terminal : CascadePhysicalStageData prepared path ⟨count - 1, by omega⟩ incomingTime extent historyMagnitude
      (1 / 16) initialError (eta / 100) eta matchingAccuracy,
      terminal.entry = 0 ∧ CascadeNextStageProducer prepared path incomingTime extent historyMagnitude (1 / 16)
        initialError (eta / 100) eta matchingAccuracy := by
  classical
  have terminalNumeric : 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
      min (min ((eta / 1000) / 4) (1 / 8) / 4) 1 / 5120 := by
    apply numericBudget.trans
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 5120)
    apply min_le_min_right
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
    exact min_le_min (half_le_self (by positivity : 0 ≤ (eta / 1000) / 4)) le_rfl
  obtain ⟨terminalThreshold, terminalThresholdPositive, terminalEighth, terminalCap, terminalCapPositive, terminalFactors⟩ :=
    exists_uniform_actual_terminal_calibrated_stage eta etaPositive etaSmall orbit normalized sectionTime initialError modelDerivative
      sectionPositive errorPositive errorSmall radiusLarge separationClose outgoing transverse earlierMargin terminalNumeric
  obtain ⟨genericThreshold, genericThresholdPositive, _, genericCap, genericCapPositive, genericFactors⟩ :=
    exists_uniform_actual_calibrated_stage etaPositive etaSmall orbit normalized sectionTime initialError modelDerivative
      sectionPositive errorPositive errorSmall radiusLarge transverse earlierMargin separationClose outgoing numericBudget
  let thresholdMax := min terminalThreshold genericThreshold
  let rawCap := min terminalCap genericCap
  have thresholdTerminal : thresholdMax ≤ terminalThreshold := min_le_left _ _
  have thresholdGeneric : thresholdMax ≤ genericThreshold := min_le_right _ _
  have capTerminal : rawCap ≤ terminalCap := min_le_left _ _
  have capGeneric : rawCap ≤ genericCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min terminalThresholdPositive genericThresholdPositive, thresholdTerminal.trans terminalEighth,
    rawCap, lt_min terminalCapPositive genericCapPositive, ?_⟩
  intro factor factorPositive factorSmall referenceSeparated
  obtain ⟨terminalRoot, terminalRootEight, terminalExtent, terminalExtentFour, terminalEndpoint, terminalEndpointPositive,
    terminalEndpointOne, terminalParameters⟩ := terminalFactors factor factorPositive factorSmall referenceSeparated
  obtain ⟨genericExtent, genericExtentFour, genericRoot, _, genericEndpoint, genericEndpointPositive, _, genericParameters⟩ :=
    genericFactors factor factorPositive factorSmall referenceSeparated
  let initialBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let initialExtent := max 4 (initialBound + 1)
  let initialMagnitude := initialBound + 2
  let extent := max initialExtent (max terminalExtent genericExtent)
  let rootMin := max terminalRoot genericRoot
  let endpointMax := min terminalEndpoint genericEndpoint
  have initialExtentBound : initialExtent ≤ extent := le_max_left _ _
  have terminalExtentBound : terminalExtent ≤ extent := (le_max_left _ _).trans (le_max_right _ _)
  have genericExtentBound : genericExtent ≤ extent := (le_max_right _ _).trans (le_max_right _ _)
  have extentFour : 4 ≤ extent := (le_max_left _ _).trans initialExtentBound
  have extentOne : 1 ≤ extent := (by norm_num : (1 : ℝ) ≤ 4).trans extentFour
  refine ⟨extent, extentFour, rootMin, terminalRootEight.trans (le_max_left _ _), endpointMax,
    lt_min terminalEndpointPositive genericEndpointPositive, (min_le_left _ _).trans terminalEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound
  filter_upwards [terminalParameters endpoint endpointPositive (endpointBound.trans (min_le_left _ _)),
    genericParameters endpoint endpointPositive (endpointBound.trans (min_le_right _ _))]
    with incomingTime terminalAt genericAt
  obtain ⟨sectionAfter, terminalMagnitude, terminalMagnitudeNonnegative, terminalAccuracy⟩ := terminalAt
  obtain ⟨_, genericTolerance, genericTolerancePositive, genericMagnitude, genericMagnitudeNonnegative, genericAccuracy⟩ := genericAt
  let historyMagnitude := max initialMagnitude (max terminalMagnitude genericMagnitude)
  have initialMagnitudeBound : initialMagnitude ≤ historyMagnitude := le_max_left _ _
  have terminalMagnitudeBound : terminalMagnitude ≤ historyMagnitude := (le_max_left _ _).trans (le_max_right _ _)
  have genericMagnitudeBound : genericMagnitude ≤ historyMagnitude := (le_max_right _ _).trans (le_max_right _ _)
  have historyNonnegative : 0 ≤ historyMagnitude := terminalMagnitudeNonnegative.trans terminalMagnitudeBound
  refine ⟨sectionAfter, historyMagnitude, historyNonnegative, ?_⟩
  intro stopTolerance stopPositive
  let matchingMax := min genericTolerance stopTolerance
  refine ⟨matchingMax, lt_min genericTolerancePositive stopPositive, min_le_right _ _, ?_⟩
  intro matchingAccuracy matchingPositive matchingBound
  have accuracyGeneric : matchingAccuracy ≤ genericTolerance := matchingBound.trans (min_le_left _ _)
  obtain ⟨terminalRatio, _, terminalScales⟩ := terminalAccuracy matchingAccuracy matchingPositive 1 zero_lt_one
  obtain ⟨genericRatio, _, genericScales⟩ := genericAccuracy matchingAccuracy matchingPositive extent historyMagnitude extentOne historyNonnegative
  let ratioMin := max 128 (max terminalRatio genericRatio)
  refine ⟨ratioMin, le_max_left _ _, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne controlledSeparation
  have ratio128 : 128 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioTwo : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 128).trans ratio128
  have terminalRatioLarge : terminalRatio ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have genericRatioLarge : genericRatio ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have terminalRootLarge : terminalRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have genericRootLarge : genericRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8)
    (terminalRootEight.trans terminalRootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 2 := ((thresholdBound.trans thresholdTerminal).trans terminalEighth).trans (by norm_num)
  have ratioSeparation : (2 * Real.sqrt 2 + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    have sqrtTwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
    nlinarith only [controlledSeparation, ratio128, sqrtTwo]
  filter_upwards [terminalScales scales scaleRoot terminalRootLarge amplitudeIdentity terminalRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdTerminal)
      boundaryConstant boundaryOne ratioSeparation,
    genericScales scales scaleRoot genericRootLarge amplitudeIdentity genericRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdGeneric)
      boundaryConstant boundaryOne controlledSeparation,
    eventually_actual_terminal_physical_stage_data orbit sectionTime incomingTime initialError errorPositive.le errorSmall radiusLarge
      separationClose outgoing extent historyMagnitude (1 / 16) (eta / 100) eta matchingAccuracy initialExtentBound initialMagnitudeBound
      (by positivity) etaPositive.le scales amplitudePositive ratio128 alphaPositive,
    scales.eventually_predictedTime_index_lt_quarter ratioTwo alphaPositive alphaSmall sectionPositive,
    eventually_ge_atTop (max 1 (8 * eta + 1))]
    with frequency terminalStep genericStep initial predictedSmall frequencyLarge
  intro count countLarge phase dipoleAngle
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le ((le_max_left _ _).trans frequencyLarge)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioTwo]
  have omegaPositive (index : Fin count) : 0 < changed.omega (index.val + 1) := changed.omega_pos frequencyPositive ratioPositive _
  have timingQuarter (index : Fin count) : eta / changed.omega (index.val + 1) < 1 / 4 := by
    apply (div_lt_iff₀ (omegaPositive index)).mpr
    have omegaLower := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioTwo]) (index.val + 1)
    have lower : 8 * eta + 1 ≤ frequency := (le_max_right _ _).trans frequencyLarge
    nlinarith only [lower, omegaLower, etaPositive]
  refine ⟨fun index => ⟨omegaPositive index, timingQuarter index, predictedSmall count (index.val + 1) (by omega)⟩, ?_⟩
  intro shapeRadius monitor prepared path prescribed
  let last : Fin count := ⟨count - 1, by omega⟩
  obtain ⟨terminalRecord, terminalZero, _, _, _⟩ := initial count countLarge phase dipoleAngle prepared path thresholdSmall last (by dsimp only [last]; omega)
  refine ⟨terminalRecord, terminalZero, ?_⟩
  intro index nonterminal prior priorOrder nearestHalf
  let drive : Fin count := ⟨index.val + 1, nonterminal⟩
  have driveFiner : index.val < drive.val := Nat.lt_succ_self _
  by_cases terminalDriver : drive.val + 1 = count
  · have sameLast : drive = last := Fin.ext (by dsimp only [last]; omega)
    have zeroFirst : FirstSeparationTime changed orbit sectionTime prepared.trajectory.movingFamily.patchMotion drive 0 := by
      have original := terminalRecord.firstSeparation
      rw [terminalZero] at original
      simpa only [sameLast] using original
    have priorZero : (prior drive driveFiner).entry = 0 := (prior drive driveFiner).firstSeparation.unique zeroFirst
    obtain ⟨localData, localPositive, _⟩ := terminalStep count phase dipoleAngle (prepared.enlargeCap capTerminal) path
      index drive rfl terminalDriver prescribed
    let returned := CascadePhysicalStageData.ofEnlargeCap prepared capTerminal path localData
    let enlarged := returned.weakenBounds terminalExtentBound terminalMagnitudeBound le_rfl le_rfl le_rfl
    refine ⟨enlarged, ?_⟩
    change (prior drive driveFiner).entry < localData.entry
    rw [priorZero]
    exact localPositive
  · have driveNonterminal : index.val + 2 < count := by dsimp only [drive] at terminalDriver; omega
    let localPrior : ∀ source : Fin count, index.val < source.val →
        CascadePhysicalStageData (prepared.enlargeCap capGeneric) path source incomingTime extent historyMagnitude (1 / 16) initialError
          (eta / 100) eta genericTolerance :=
      fun source finer => CascadePhysicalStageData.toEnlargeCap prepared capGeneric path
        ((prior source finer).weakenBounds le_rfl le_rfl le_rfl le_rfl accuracyGeneric)
    have localOrder (source : Fin count) (finer : index.val < source.val) :
        (localPrior source finer).entry ≤ (localPrior drive driveFiner).entry := by
      change (prior source finer).entry ≤ (prior drive driveFiner).entry
      by_cases equal : source = drive
      · subst source; exact le_rfl
      · have later : drive.val < source.val := by
          have different : source.val ≠ drive.val := fun h => equal (Fin.ext h)
          dsimp only [drive] at different ⊢
          omega
        exact (priorOrder drive source driveFiner finer later).le
    have localHalf : (localPrior drive driveFiner).entry ≤ 1 / 2 := nearestHalf
    have rates (source : Fin count) (finer : index.val < source.val) :
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ (1 / 16 : ℝ) * changed.omega (source.val + 1) := by
      have monotone : changed.omega (index.val + 1) * changed.ratio ≤ changed.omega (source.val + 1) := by
        unfold Scales.omega
        change frequency * scales.ratio ^ (index.val + 1) * scales.ratio ≤ frequency * scales.ratio ^ (source.val + 1)
        rw [mul_assoc, ← pow_succ]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith only [ratioTwo] : 1 ≤ scales.ratio) (by omega)) frequencyPositive.le
      have coefficientBound : 4 * Real.sqrt 2 ≤ (1 / 16 : ℝ) * changed.ratio := by
        have sqrtTwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
        change 4 * Real.sqrt 2 ≤ (1 / 16 : ℝ) * scales.ratio
        linarith only [ratio128, sqrtTwo]
      calc
        _ = (4 * Real.sqrt 2) * changed.omega (index.val + 1) := by ring
        _ ≤ ((1 / 16 : ℝ) * changed.ratio) * changed.omega (index.val + 1) :=
          mul_le_mul_of_nonneg_right coefficientBound (omegaPositive index).le
        _ = (1 / 16 : ℝ) * (changed.omega (index.val + 1) * changed.ratio) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left monotone (by norm_num)
    obtain ⟨localData, entryOrder, _⟩ := genericStep count phase dipoleAngle (prepared.enlargeCap capGeneric) path prescribed index nonterminal
      driveNonterminal localPrior localOrder localHalf rates
    let returned := CascadePhysicalStageData.ofEnlargeCap prepared capGeneric path localData
    let enlarged := returned.weakenBounds genericExtentBound genericMagnitudeBound le_rfl le_rfl le_rfl
    refine ⟨enlarged, ?_⟩
    exact entryOrder

end EulerNonuniqueness.Paper
