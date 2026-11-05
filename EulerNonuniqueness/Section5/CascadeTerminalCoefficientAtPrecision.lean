import EulerNonuniqueness.Section5.CascadeTerminalFinerInitialData
import EulerNonuniqueness.Section5.CascadeGivenMapIncomingWeightedErrorsAtPrecision
import EulerNonuniqueness.Section6.SourcePacketTerminalControlledSignedWindow
import EulerNonuniqueness.Section5.CascadeTerminalSourcePhase
import EulerNonuniqueness.Section5.CascadeIncomingDuhamelCoefficient
import EulerNonuniqueness.Section1.SeedFixedLevelHitElapsed

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_terminal_coefficient_at_precision
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (sectionTime initialError : ℝ)
    (errorNonnegative : 0 ≤ initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 → ∃ rootMin ≥ (8 : ℝ),
    ∀ fullMagnitude sharpMagnitude : ℝ, 0 ≤ fullMagnitude → 0 ≤ sharpMagnitude →
    ∀ tolerance : ℝ, 0 < tolerance →
    let windowTolerance := min (tolerance / 4) (1 / 8)
    20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤ min (windowTolerance / 4) 1 / 5120 →
    ∃ coarsePrecision > (0 : ℝ), ∃ endpointMax > (0 : ℝ), endpointMax ≤ 1 ∧
    ∀ endpoint : ℝ, 0 < endpoint → endpoint ≤ endpointMax → ∀ level : ℝ, 0 < level →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ boundaryConstant : ℝ, 1 ≤ boundaryConstant →
    (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index source : Fin count, index.val + 1 = source.val → source.val + 1 = count →
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ hit ∈ Icc 0 path.stop,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let seed := changed.seed (index.val + 1)
    let actualQ := (referenceStraightenedShape motion graph coordinate index hit -
      referenceStraightenedShape prepared.reference graph coordinate index hit).1
    actualQ = level →
    (∀ current : Fin count, current.val ≤ index.val → ∀ time ∈ Icc 0 hit,
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4) →
    ∀ lift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (lift side) (Icc 0 hit)) →
    (∀ side, lift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 hit,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ))) →
    (∀ time ∈ Icc 0 hit, prepared.finiteCoordinateSize graph coordinate lift index time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        fullMagnitude * seed * Real.exp (growth * time)) →
    (∀ time ∈ Icc 0 hit, prepared.rawSourceCenteredState time index +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
      ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
        sharpMagnitude * seed * Real.exp (growth * time)) →
    ∀ coarseLift : Fin count → Fin 2 → ℝ → ℝ,
    (∀ current : Fin count, current.val < index.val → ∀ time ∈ Icc 0 hit,
      prepared.finiteCoordinateSize graph coordinate (coarseLift current) current time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch ≤ coarsePrecision) →
    seed * Real.exp (growth * hit) ≤ endpoint →
    let coefficient := Real.exp (-growth * hit) * actualQ / seed
    |coefficient - 1| ≤ tolerance ∧ 0 < coefficient ∧ seed * coefficient * Real.exp (growth * hit) = level := by
  classical
  obtain ⟨errorThreshold, errorThresholdPositive, errorEighth, rawCap, capPositive, errorFactors⟩ :=
    exists_uniform_actual_given_map_incoming_weighted_errors_at_precision graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨_, _, windowThreshold, windowThresholdPositive, _, windows⟩ :=
    exists_actual_terminal_controlled_signed_window orbit sectionTime initialError errorNonnegative errorSmall radiusLarge separationClose outgoing
  obtain ⟨physicalRadius, physicalPositive, _, coefficients⟩ :=
    exists_uniform_actual_incoming_duhamel_coefficient graphAnalytic.contDiffAt coordinateSmooth
  obtain ⟨physicalPrecision, physicalPrecisionPositive, refinePhysical⟩ :=
    exists_uniform_actual_full_state_physical_refinement graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative physicalPositive
  let thresholdMax := min errorThreshold windowThreshold
  have thresholdPositive : 0 < thresholdMax := lt_min errorThresholdPositive windowThresholdPositive
  refine ⟨thresholdMax, thresholdPositive, (min_le_left _ _).trans errorEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨rootMin, rootEight, magnitudes⟩ := errorFactors factor factorPositive factorSmall
  refine ⟨rootMin, rootEight, ?_⟩
  intro fullMagnitude sharpMagnitude fullNonnegative sharpNonnegative tolerance tolerancePositive
  dsimp only
  intro numericBudget
  let windowTolerance := min (tolerance / 4) (1 / 8)
  have windowPositive : 0 < windowTolerance := by dsimp only [windowTolerance]; positivity
  have windowEighth : windowTolerance ≤ 1 / 8 := min_le_right _ _
  have windowQuarter : windowTolerance ≤ tolerance / 4 := min_le_left _ _
  obtain ⟨coarsePrecision, coarsePositive, errorEndpoint, errorEndpointPositive, errorEndpointOne, parameters⟩ :=
    magnitudes fullMagnitude sharpMagnitude fullNonnegative sharpNonnegative (tolerance / 4) (by positivity)
  let endpointMax := min errorEndpoint (physicalPrecision / (fullMagnitude + 1))
  have endpointMaxPositive : 0 < endpointMax := by dsimp only [endpointMax]; positivity
  have endpointErrors : endpointMax ≤ errorEndpoint := min_le_left _ _
  have endpointPhysical : endpointMax ≤ physicalPrecision / (fullMagnitude + 1) := min_le_right _ _
  refine ⟨coarsePrecision, coarsePositive, endpointMax, endpointMaxPositive, endpointErrors.trans errorEndpointOne, ?_⟩
  intro endpoint endpointPositive endpointBound level levelPositive
  let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := max 4 (modelBound + 1)
  let magnitude := modelBound + 2
  have boundThree : 3 ≤ modelBound := le_max_left _ _
  have extentOne : 1 ≤ extent := (by norm_num : (1 : ℝ) ≤ 4).trans (le_max_left _ _)
  have magnitudeNonnegative : 0 ≤ magnitude := by dsimp only [magnitude]; linarith only [boundThree]
  obtain ⟨errorRatio, errorRatioTwo, errorScales⟩ := parameters extent magnitude (separationRadius orbit sectionTime) (1 / 16)
    extentOne magnitudeNonnegative (by linarith only [radiusLarge]) (by norm_num)
  let windowRatio := max (max 2 (65536 / windowTolerance)) (24 * separationRadius orbit sectionTime / windowTolerance)
  let ratioMin := max errorRatio (max 128 windowRatio)
  refine ⟨ratioMin, errorRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have errorRatioLarge : errorRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratio128 : 128 ≤ scales.ratio := (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
  have windowRatioLarge : windowRatio ≤ scales.ratio := (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
  have ratioBound : 2 ≤ scales.ratio := errorRatioTwo.trans errorRatioLarge
  have windowRatioBound : max 2 (65536 / windowTolerance) ≤ scales.ratio := (le_max_left _ _).trans windowRatioLarge
  have windowBudget : 12 * separationRadius orbit sectionTime ≤ (windowTolerance / 2) * scales.ratio := by
    have bound := (div_le_iff₀ windowPositive).mp ((le_max_right _ _).trans windowRatioLarge)
    nlinarith only [bound]
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdErrors : threshold ≤ errorThreshold := thresholdBound.trans (min_le_left _ _)
  have thresholdWindow : threshold ≤ windowThreshold := thresholdBound.trans (min_le_right _ _)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdErrors.trans errorEighth
  let elapsedMin := max 1 (272 / (3 * tolerance))
  filter_upwards [errorScales scales scaleRoot rootLarge amplitudeIdentity errorRatioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdErrors orbit sectionTime boundaryConstant 0 boundaryOne le_rfl ratioSeparation,
    eventually_actual_terminal_finer_initial_data orbit sectionTime initialError errorNonnegative errorSmall radiusLarge
      separationClose outgoing scales amplitudePositive ratio128 alphaPositive,
    windows windowTolerance windowPositive windowEighth numericBudget scales amplitudePositive alphaPositive windowRatioBound windowBudget
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdWindow factor scaleRoot boundaryConstant factorPositive
      (factorSmall.trans (by norm_num)) rootOne boundaryOne,
    coefficients scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive (factorSmall.trans (by norm_num)),
    refinePhysical scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative (by positivity : 0 < physicalRadius / 8),
    scales.eventually_fixed_level_hit_elapsed_gt ratioBound alphaPositive levelPositive fullNonnegative elapsedMin,
    eventually_gt_atTop (0 : ℝ)] with frequency errors finerData window coefficientEstimate physical referenceSmall elapsed frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index source adjacent terminal prescribed hit hitInside
  intro hitIdentity weakPhysical lift liftContinuous liftInitial liftPolar fullProfile sharpProfile coarseLift coarseFull exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let seed := changed.seed (index.val + 1)
  have nonterminal : index.val + 1 < count := by omega
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    dsimp only [growth]; positivity
  obtain ⟨_, _, entries, extents, sourceProfiles, domains, rateGaps, nearestTiming, sourceTiming⟩ :=
    finerData count phase dipoleAngle prepared path (thresholdSmall.trans (by norm_num)) index source adjacent terminal
  let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
  have weighted := errors count phase dipoleAngle prepared path index nonterminal
    (fun _ => 0) (fun _ => separationRadius orbit sectionTime) (fun _ => direction) entries extents (fun _ => magnitude)
    (by intro current finer; exact ⟨magnitudeNonnegative, sourceProfiles current finer⟩)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) domains (fun _ => 0) (fun _ => rfl) nearestTiming sourceTiming
    (fun _ _ => le_rfl) hit hitInside weakPhysical lift liftContinuous liftInitial liftPolar rateGaps
    (by simpa only [sub_zero] using fullProfile) (by simpa only [sub_zero] using sharpProfile)
    coarseLift coarseFull (by simpa only [sub_zero] using exposure.trans (endpointBound.trans endpointErrors))
  dsimp only at weighted
  have remainderSmall := weighted.2.2.1
  have coarseSmall := weighted.2.2.2.2.2.2
  simp only [mul_zero, Real.exp_zero, one_mul] at remainderSmall coarseSmall
  have fullSmall (time : ℝ) (inside : time ∈ Icc 0 hit) :
      prepared.finiteCoordinateSize graph coordinate lift index time + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤ physicalPrecision := by
    have qBound : seed * Real.exp (growth * time) ≤ endpoint :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left inside.2 growthPositive.le)) seedPositive.le).trans exposure
    have product := (le_div_iff₀ (by positivity : 0 < fullMagnitude + 1)).mp (endpointBound.trans endpointPhysical)
    have magnitudeBound : fullMagnitude * endpoint ≤ physicalPrecision := by nlinarith only [product, endpointPositive]
    have actual := fullProfile time inside
    change _ ≤ fullMagnitude * seed * Real.exp (growth * time) at actual
    exact actual.trans (by
      have scaled := mul_le_mul_of_nonneg_left qBound fullNonnegative
      simpa only [mul_assoc] using scaled.trans magnitudeBound)
  have refined := physical prepared path factorPositive index nonterminal hit hitInside (weakPhysical index le_rfl) lift fullSmall
  have pairedPhysical (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 hit) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < physicalRadius := by
    fin_cases side
    · exact refined time inside
    · have reference := referenceSmall prepared.toCascadeMaterialPreparedPair time ⟨inside.1, inside.2.trans (hitInside.2.trans path.stopBound)⟩ index
      have unused := abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < physicalRadius
      linarith only [reference, unused, physicalPositive]
  have fullDominates : level ≤ prepared.finiteCoordinateSize graph coordinate lift index hit +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget hit index patch := by
    have identity : (referenceStraightenedShape motion graph coordinate index hit).1 -
      (referenceStraightenedShape prepared.reference graph coordinate index hit).1 = level := hitIdentity
    have firstBound : level ≤ |(referenceStraightenedShape motion graph coordinate index hit).1 -
        (referenceStraightenedShape prepared.reference graph coordinate index hit).1| := by
      rw [identity]
      exact le_abs_self level
    have locationPositive := changed.location_pos (index.val + 1)
    have lengthPositive := changed.length_pos (index.val + 1)
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
    have extra : 0 ≤ |(referenceStraightenedShape motion graph coordinate index hit).2 -
        (referenceStraightenedShape prepared.reference graph coordinate index hit).2| +
      |diagonalDifference motion hit index - diagonalDifference prepared.reference hit index| / changed.length (index.val + 1) ^ 2 +
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index hit| +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference index hit‖ +
      ‖quadrupoleCenter motion hit index - quadrupoleCenter prepared.reference hit index‖ / changed.location (index.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget hit index patch := by
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    linarith only [firstBound, extra]
  have elapsedLarge : elapsedMin < growth * hit := elapsed (index.val + 1) (growth * hit)
    (by
      have actual := fullProfile hit ⟨hitInside.1, le_rfl⟩
      change _ ≤ fullMagnitude * seed * Real.exp (growth * hit) at actual
      exact fullDominates.trans actual)
  have exponentialLarge : 68 / tolerance ≤ Real.exp ((3 * growth / 4) * hit) := by
    have bound : 272 / (3 * tolerance) ≤ elapsedMin := le_max_right _ _
    have scaled := (div_le_iff₀ (by positivity : 0 < 3 * tolerance)).mp bound
    have linear := Real.add_one_le_exp ((3 * growth / 4) * hit)
    apply (div_le_iff₀ tolerancePositive).mpr
    have elapsedScaled := mul_le_mul_of_nonneg_right elapsedLarge.le tolerancePositive.le
    nlinarith only [scaled, elapsedScaled, mul_le_mul_of_nonneg_right linear tolerancePositive.le, tolerancePositive]
  have tail : 17 * Real.exp (-(3 * growth / 4) * hit) ≤ tolerance / 4 := by
    have reciprocal := one_div_le_one_div_of_le (by positivity : 0 < 68 / tolerance) exponentialLarge
    have same : -(3 * growth / 4) * hit = -((3 * growth / 4) * hit) := by ring
    rw [same, Real.exp_neg]
    have scaled := mul_le_mul_of_nonneg_left reciprocal (by norm_num : (0 : ℝ) ≤ 17)
    have identity : 17 * (1 / (68 / tolerance)) = tolerance / 4 := by field_simp; ring
    simpa only [one_div] using scaled.trans_eq identity
  obtain ⟨_, _, _, windowAt⟩ := window count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index source adjacent terminal
  have nearest := (windowAt hit hitInside.1 hitInside.2).2.1
  have phaseIdentity := prescribed.terminal_source_residual_cos index source adjacent terminal
  dsimp only at phaseIdentity nearest
  rw [phaseIdentity] at nearest
  have nearestClose : |(∫ time in (0 : ℝ)..hit, Real.exp (-growth * time) *
      (relativeBlockSourceShapeInput changed motion prepared.reference index source time).1) / seed - 1| ≤ tolerance / 2 :=
    nearest.trans (by linarith only [windowQuarter, tail])
  have olderEmpty : Finset.univ.filter (fun current : Fin count => source.val < current.val) = ∅ := by
    ext current
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty, iff_false]
    omega
  have result := coefficientEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index source adjacent
    hit hitInside.1 hitInside.2 pairedPhysical 0 0 level (tolerance / 2) (tolerance / 4) 0 (tolerance / 4) levelPositive
    hitIdentity (by simpa only [mul_zero, Real.exp_zero, one_mul, Real.cos_zero] using nearestClose)
    (by simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul, div_eq_mul_inv, mul_comm] using coarseSmall)
    (by simp only [olderEmpty, Finset.sum_empty, norm_zero, mul_zero, intervalIntegral.integral_zero, zero_mul, le_refl])
    (by simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul, div_eq_mul_inv, mul_comm] using remainderSmall)
  dsimp only at result
  simp only [sub_zero, Real.cos_zero] at result
  refine ⟨result.1.trans_eq (by ring), result.2⟩

end EulerNonuniqueness.Paper
