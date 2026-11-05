import EulerNonuniqueness.Section5.CascadeFiniteCoordinateLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeLeadingStrainContinuity
import EulerNonuniqueness.General.FiniteStateNeutralHistoryMajorants

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_neutral_original_history
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ), ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    rootMin ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let size := prepared.finiteCoordinateSize graph coordinate suppliedLift index
    let shape := fun time =>
      |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let forcing := prepared.finiteCoordinateForeignForcing index
    let budget := fun time => changed.omega (index.val + 1) * (size time + epsilon * raw time) + forcing time
    ContinuousOn size (Icc 0 finish) ∧ size 0 = 0 ∧ ContinuousOn forcing (Icc 0 finish) ∧
    IntervalIntegrable forcing volume 0 finish ∧ IntervalIntegrable budget volume 0 finish ∧
    ∀ time ∈ Icc 0 finish, size time ≤ shape time + constant * ∫ current in (0 : ℝ)..time, budget current := by
  obtain ⟨geometryRadius, geometryPositive, geometryQuarter, geometryConstant, geometryOne, geometryFactory⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨phaseThreshold, phaseThresholdPositive, phaseThresholdEighth, phaseCap, phaseCapPositive, phaseFactory⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_history graphAnalytic graphZero graphDerivative coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨momentCap, momentCapPositive, momentFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_history
  obtain ⟨dilationCap, dilationCapPositive, dilationFactory⟩ := exists_uniform_actual_prehit_dilation_local_foreign_history
  obtain ⟨centerCap, centerCapPositive, centerFactory⟩ := exists_uniform_actual_center_local_foreign_history
  obtain ⟨stateCap, stateCapPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min momentCap (min dilationCap (min phaseCap (min centerCap stateCap)))
  have capPositive : 0 < rawCap := lt_min momentCapPositive (lt_min dilationCapPositive (lt_min phaseCapPositive (lt_min centerCapPositive stateCapPositive)))
  have capMoment : rawCap ≤ momentCap := min_le_left _ _
  have capDilation : rawCap ≤ dilationCap := (min_le_right _ _).trans (min_le_left _ _)
  have capPhase : rawCap ≤ phaseCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have capCenter : rawCap ≤ centerCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have capState : rawCap ≤ stateCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨phaseThreshold, phaseThresholdPositive, phaseThresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨momentConstant, momentNonnegative, momentParameters⟩ := momentFactory factorPositive factorEighth
  obtain ⟨dilationConstant, dilationNonnegative, dilationParameters⟩ := dilationFactory factorPositive factorSmall
  obtain ⟨phaseConstant, phaseNonnegative, phaseParameters⟩ := phaseFactory factorPositive factorEighth
  obtain ⟨phaseRadius, phasePositive, _, phaseParameters⟩ := phaseParameters 1 (by norm_num)
  obtain ⟨centerConstant, centerNonnegative, centerParameters⟩ := centerFactory factorPositive factorSmall
  let bound := 1 + geometryConstant + momentConstant + dilationConstant + phaseConstant + centerConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith only [geometryOne, momentNonnegative, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundGeometry : geometryConstant ≤ bound := by dsimp only [bound]; linarith only [momentNonnegative, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundMoment : momentConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, dilationNonnegative, phaseNonnegative, centerNonnegative]
  have boundDilation : dilationConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, momentNonnegative, phaseNonnegative, centerNonnegative]
  have boundPhase : phaseConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, momentNonnegative, dilationNonnegative, centerNonnegative]
  have boundCenter : centerConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, momentNonnegative, dilationNonnegative, phaseNonnegative]
  let radius := min geometryRadius phaseRadius
  have radiusQuarter : radius ≤ 1 / 4 := (min_le_left _ _).trans geometryQuarter
  have constantOne : 1 ≤ 40 * bound ^ 2 := by nlinarith only [boundOne, sq_nonneg (bound - 1)]
  refine ⟨radius, lt_min geometryPositive phasePositive, radiusQuarter, 40 * bound ^ 2, constantOne, 8, le_rfl, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant rootLarge boundaryOne thresholdBound referenceNonnegative
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans rootLarge
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans phaseThresholdEighth
  filter_upwards [geometryFactory scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne)
      factorPositive factorEighth thresholdSmall referenceNonnegative,
    momentParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    dilationParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    phaseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdBound referenceNonnegative,
    centerParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_patch_external_velocity_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_length_lt_location ratioBound alphaPositive (show (0 : ℝ) < factor / 39321600 by positivity),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency geometryEstimate momentEstimate dilationEstimate phaseEstimate centerEstimate seriesContinuous coherence externalContinuous leadingRegular lengths radii strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  have centeredCapInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let macroRadius := factor / 39321600 * changed.location (index.val + 1)
  let ownRadius := factor / 39321600 * changed.length (index.val + 1)
  let relative := fun time => referenceStraightenedShape first graph coordinate index time - referenceStraightenedShape second graph coordinate index time
  let shape := fun time => |(relative time).1| + |(relative time).2|
  let dilation := fun time => |diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time index
  let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time macroRadius power - quadrupoleExteriorCoefficient changed second index time macroRadius power‖
  let foreign := fun receiverRadius (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first current index patch) receiverRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch) receiverRadius (power + 1) time‖
  let external := fun time => (∑ patch : Fin 4, ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
    biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * changed.location (index.val + 1))
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonOne : epsilon ≤ 1 := by
    have radiusBound := (radii (index.val + 1)).le
    change changed.radius (index.val + 1) ≤ 1 * changed.length (index.val + 1) at radiusBound
    exact (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
      (pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le (by simpa only [one_mul] using radiusBound) 2)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have ratioOne : changed.length (index.val + 1) / changed.location (index.val + 1) ≤ 1 := by
    apply (div_le_one (changed.location_pos _)).mpr
    have actual := (lengths (index.val + 1)).le
    have coefficient : factor / 39321600 ≤ (1 : ℝ) := by linarith only [factorSmall]
    exact actual.trans (mul_le_of_le_one_left (changed.location_pos _).le coefficient)
  have radialSmall : ∀ time ∈ Icc 0 finish, |radialShape first time index| ≤ 1 / 2 := by
    intro time inside
    have identity : radialShape first time index = unstableShape first time index + stableShape first time index := by unfold unstableShape stableShape; ring
    rw [identity]
    exact (abs_add_le _ _).trans ((small time inside).trans (radiusQuarter.trans (by norm_num)))
  obtain ⟨lift, liftContinuous, polar, coordinateContinuous, coordinateInitial, _, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound (fun time inside => (small time inside).trans (min_le_left _ _))
  have geometryEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusQuarter) lift suppliedLift
    (fun side => (liftContinuous side).1.continuousOn) suppliedContinuous
    (fun side => (liftContinuous side).2.trans (suppliedInitial side).symm) polar suppliedPolar).2.2 graph coordinate
  have sizeContinuous := coordinateContinuous.congr (fun time inside => (geometryEquality inside).symm)
  have sizeInitial : prepared.finiteCoordinateSize graph coordinate suppliedLift index 0 = 0 :=
    (geometryEquality ⟨le_rfl, finishNonnegative⟩).symm.trans coordinateInitial
  let size := prepared.finiteCoordinateSize graph coordinate suppliedLift index
  let phaseValue := fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|
  let translation := fun time => ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1)
  let forcing := prepared.finiteCoordinateForeignForcing index
  let budget := fun time => omega * (size time + epsilon * raw time) + forcing time
  have sizeIdentity (time : ℝ) : size time = shape time + dilation time + phaseValue time + moment time + translation time := by
    dsimp only [size, shape, relative, dilation, phaseValue, moment, translation, CascadeSourcePreparedPair.finiteCoordinateSize, first, second, changed, Prod.fst_sub, Prod.snd_sub]
  have forcingIdentity (time : ℝ) : forcing time = ‖leading time‖ + difference time + epsilon * (∑ patch : Fin 4, foreign macroRadius patch time) +
      epsilon * (∑ patch : Fin 4, foreign ownRadius patch time) + external time := by
    dsimp only [forcing, CascadeSourcePreparedPair.finiteCoordinateForeignForcing, leading, difference, foreign, macroRadius, ownRadius, epsilon, external, first, second, changed]
    rw [prepared.referenceIdentity]
  have allNonnegative (time : ℝ) : 0 ≤ shape time ∧ 0 ≤ dilation time ∧ 0 ≤ phaseValue time ∧ 0 ≤ moment time ∧ 0 ≤ translation time ∧
      0 ≤ center time ∧ 0 ≤ raw time ∧ 0 ≤ difference time ∧ (∀ receiverRadius, 0 ≤ ∑ patch : Fin 4, foreign receiverRadius patch time) ∧ 0 ≤ external time := by
    refine ⟨add_nonneg (abs_nonneg _) (abs_nonneg _), div_nonneg (abs_nonneg _) (sq_nonneg _), abs_nonneg _, norm_nonneg _,
      div_nonneg (norm_nonneg _) (changed.location_pos _).le, div_nonneg (norm_nonneg _) (changed.length_pos _).le,
      ?_, tsum_nonneg (fun _ => norm_nonneg _), ?_, div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (mul_nonneg (by norm_num) (changed.location_pos _).le)⟩
    · apply Finset.sum_nonneg
      intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    · intro receiverRadius
      exact Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _)))
  have leadingContinuous := (leadingRegular count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index).mono subset
  have momentHistory := momentEstimate count phase dipoleAngle (prepared.enlargeCap capMoment) path index nonterminal finish finishNonnegative finishBound radialSmall
  have dilationHistory := dilationEstimate count phase dipoleAngle (prepared.enlargeCap capDilation) path index nonterminal finish finishNonnegative finishBound radialSmall
  have centerHistory := centerEstimate count phase dipoleAngle (prepared.enlargeCap capCenter) path index nonterminal finish finishNonnegative finishBound radialSmall
  have phaseHistory := phaseEstimate count phase dipoleAngle (prepared.enlargeCap capPhase) path index nonterminal finish finishNonnegative finishBound radialSmall
    (fun time inside => (small time inside).trans (min_le_right _ _))
  simp only [centeredCapInvariant, rawCapInvariant] at momentHistory dilationHistory centerHistory phaseHistory
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at momentHistory dilationHistory centerHistory phaseHistory
  rw [← prepared.referenceIdentity] at momentHistory dilationHistory centerHistory
  obtain ⟨phaseLift, phaseLiftContinuous, _, phasePolar, _, _, _, _, _, _, _, phaseUpperIntegrable, _, phasePrimitive⟩ := phaseHistory
  have phaseEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusQuarter) suppliedLift phaseLift
    suppliedContinuous (fun side => (phaseLiftContinuous side).1.continuousOn)
    (fun side => (suppliedInitial side).trans (phaseLiftContinuous side).2.symm) suppliedPolar phasePolar).2.1 (phaseCorrection 1 graph)
  have radiusSmall (receiverRadius : ℝ) (nonnegative : 0 ≤ receiverRadius) (upper : receiverRadius ≤ macroRadius) :
      receiverRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have locationPositive := changed.location_pos (index.val + 1)
    change receiverRadius ≤ changed.location (index.val + 1) / (100000 * 96)
    dsimp only [macroRadius] at upper
    nlinarith only [upper, locationPositive, mul_nonneg (sub_nonneg.mpr factorSmall) locationPositive.le]
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos _).le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.length_pos _).le
  have ownMacro : ownRadius ≤ macroRadius := mul_le_mul_of_nonneg_left
    ((div_le_one (changed.location_pos _)).mp ratioOne) (div_nonneg factorPositive.le (by norm_num))
  have seriesMacro := seriesContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index macroRadius macroNonnegative
    (radiusSmall macroRadius macroNonnegative le_rfl)
  have seriesOwn := seriesContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index ownRadius ownNonnegative
    (radiusSmall ownRadius ownNonnegative ownMacro)
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := by
    have actual := seriesMacro.2.2.mono subset
    rw [← prepared.referenceIdentity] at actual
    exact actual
  have foreignContinuous (receiverRadius : ℝ) (which : receiverRadius = macroRadius ∨ receiverRadius = ownRadius) :
      ContinuousOn (fun time => ∑ patch : Fin 4, foreign receiverRadius patch time) (Icc 0 finish) := by
    rcases which with rfl | rfl
    · exact continuousOn_finset_sum _ (fun patch _ => ((seriesMacro.1 patch).2.mono subset))
    · exact continuousOn_finset_sum _ (fun patch _ => ((seriesOwn.1 patch).2.mono subset))
  have externalC0 : ContinuousOn external (Icc 0 finish) := by
    have actual := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
      (externalContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).norm.mono subset)
    rw [← prepared.referenceIdentity] at actual
    exact actual.div_const _
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := by
    apply ((((leadingContinuous.norm.add differenceContinuous).add
      (continuousOn_const.mul (foreignContinuous macroRadius (Or.inl rfl)))).add
      (continuousOn_const.mul (foreignContinuous ownRadius (Or.inr rfl)))).add externalC0).congr
    intro time _
    exact forcingIdentity time
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((stateContinuity prepared capPositive capState path index).1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) := (stateContinuity prepared capPositive capState path index).2.1.mono subset
  have budgetContinuous : ContinuousOn budget (Icc 0 finish) :=
    (continuousOn_const.mul (sizeContinuous.add (continuousOn_const.mul rawContinuous))).add forcingContinuous
  have budgetNonnegative (time : ℝ) : 0 ≤ budget time := by
    rw [show budget time = omega * (size time + epsilon * raw time) + forcing time from rfl, forcingIdentity]
    obtain ⟨_, _, _, _, _, _, rawNonnegative, differenceNonnegative, foreignNonnegative, externalNonnegative⟩ := allNonnegative time
    have ownNonnegative' := foreignNonnegative ownRadius
    have macroNonnegative' := foreignNonnegative macroRadius
    have sizeNonnegative : 0 ≤ size time := by dsimp only [size, CascadeSourcePreparedPair.finiteCoordinateSize]; positivity
    exact add_nonneg (mul_nonneg omegaNonnegative (add_nonneg sizeNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)))
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) differenceNonnegative)
        (mul_nonneg epsilonNonnegative macroNonnegative')) (mul_nonneg epsilonNonnegative ownNonnegative')) externalNonnegative)
  let momentUpper := fun time => momentConstant * (changed.strain * center time + difference time + epsilon *
    (changed.strain * raw time + ∑ patch : Fin 4, foreign macroRadius patch time))
  let dilationUpper := fun time => moment time + (1 + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * center time +
    dilationConstant * omega * epsilon * raw time + dilationConstant * difference time + dilationConstant * epsilon * ∑ patch : Fin 4, foreign ownRadius patch time
  let phaseUpper := fun time => 2 * omega * dilation time + omega * shape time + (moment time + center time + shape time) +
    phaseConstant * omega * epsilon * (center time + raw time) + phaseConstant * difference time + phaseConstant * epsilon * ∑ patch : Fin 4, foreign ownRadius patch time
  let centerUpper := fun time => moment time + center time + external time + centerConstant * omega *
    (changed.length (index.val + 1) / changed.location (index.val + 1)) * epsilon * (center time + raw time) +
    centerConstant * (changed.length (index.val + 1) / changed.location (index.val + 1)) * epsilon * ∑ patch : Fin 4, foreign ownRadius patch time
  have scalarBounds (time : ℝ) (inside : time ∈ Icc 0 finish) :
      momentUpper time ≤ 7 * bound ^ 2 * budget time ∧ dilationUpper time ≤ 7 * bound ^ 2 * budget time ∧
      phaseUpper time ≤ 13 * bound ^ 2 * budget time ∧ centerUpper time ≤ 11 * bound ^ 2 * budget time := by
    obtain ⟨shapeNonnegative, dilationNonnegative', phaseNonnegative', momentNonnegative', translationNonnegative,
      centerNonnegative', rawNonnegative, differenceNonnegative, foreignNonnegative, externalNonnegative⟩ := allNonnegative time
    have shapeSize : shape time ≤ size time := by rw [sizeIdentity]; linarith only [dilationNonnegative', phaseNonnegative', momentNonnegative', translationNonnegative]
    have dilationSize : dilation time ≤ size time := by rw [sizeIdentity]; linarith only [shapeNonnegative, phaseNonnegative', momentNonnegative', translationNonnegative]
    have momentSize : moment time ≤ size time := by rw [sizeIdentity]; linarith only [shapeNonnegative, dilationNonnegative', phaseNonnegative', translationNonnegative]
    have sizeNonnegative : 0 ≤ size time := shapeNonnegative.trans shapeSize
    have centerSize := ((geometryBounds time inside).1.trans_eq (by rw [geometryEquality inside])).trans
      (mul_le_mul_of_nonneg_right boundGeometry sizeNonnegative)
    have actual := General.finite_state_neutral_history_majorants boundOne omegaOne epsilonNonnegative epsilonOne strainNonnegative strainSmall.le
      (div_nonneg (changed.length_pos _).le (changed.location_pos _).le) ratioOne
      shapeNonnegative shapeSize dilationNonnegative' dilationSize momentNonnegative' momentSize centerNonnegative' centerSize
      rawNonnegative (norm_nonneg (leading time)) differenceNonnegative (foreignNonnegative ownRadius) (foreignNonnegative macroRadius)
      externalNonnegative momentNonnegative boundMoment dilationNonnegative boundDilation phaseNonnegative boundPhase centerNonnegative boundCenter
    dsimp only [momentUpper, dilationUpper, phaseUpper, centerUpper, budget]
    rw [forcingIdentity]
    exact actual
  have momentUpperContinuous : ContinuousOn momentUpper (Icc 0 finish) := by
    dsimp only [momentUpper]
    exact continuousOn_const.mul ((continuousOn_const.mul centerContinuous).add differenceContinuous |>.add
      (continuousOn_const.mul ((continuousOn_const.mul rawContinuous).add (foreignContinuous macroRadius (Or.inl rfl)))))
  have momentUpperIntegrable := momentUpperContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  obtain ⟨_, _, _, _, _, dilationUpperIntegrable, dilationPrimitive⟩ := dilationHistory
  obtain ⟨_, _, _, _, centerUpperIntegrable, centerPrimitive⟩ := centerHistory
  have dilationI : IntervalIntegrable dilationUpper volume 0 finish := by
    simpa only [dilationUpper, moment, center, raw, difference, foreign, macroRadius, ownRadius, epsilon, omega,
      first, second, changed, one_mul, prepared.referenceIdentity] using dilationUpperIntegrable
  have phaseI : IntervalIntegrable phaseUpper volume 0 finish := by
    simpa only [phaseUpper, dilation, moment, center, raw, difference, foreign, macroRadius, ownRadius, epsilon, omega,
      shape, relative, first, second, changed, one_mul, one_add_one_eq_two, Prod.fst_sub, Prod.snd_sub, abs_div,
      abs_pow, sq_abs, prepared.referenceIdentity] using phaseUpperIntegrable
  have centerI : IntervalIntegrable centerUpper volume 0 finish := by
    simpa only [centerUpper, moment, center, raw, external, foreign, ownRadius, epsilon, omega,
      first, second, changed, one_mul, prepared.referenceIdentity] using centerUpperIntegrable
  refine ⟨sizeContinuous, sizeInitial, forcingContinuous,
    forcingContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative,
    budgetContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative, ?_⟩
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have prefixSet : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]; exact prefixSubset
  let history := ∫ current in (0 : ℝ)..time, budget current
  have historyNonnegative : 0 ≤ history := intervalIntegral.integral_nonneg inside.1 (fun current _ => budgetNonnegative current)
  have compare {upper : ℝ → ℝ} {coefficient : ℝ} (integrable : IntervalIntegrable upper volume 0 finish)
      (bounded : ∀ current ∈ Icc 0 finish, upper current ≤ coefficient * budget current) :
      (∫ current in (0 : ℝ)..time, upper current) ≤ coefficient * history := by
    have actual := intervalIntegral.integral_mono_on inside.1 (integrable.mono_set prefixSet)
      ((continuousOn_const.mul (budgetContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1)
      (fun current member => bounded current (prefixSubset member))
    simpa only [intervalIntegral.integral_const_mul, history] using actual
  have momentBound : moment time ≤ 7 * bound ^ 2 * history := by
    apply le_trans _ (compare momentUpperIntegrable (fun current member => (scalarBounds current member).1))
    simpa only [momentUpper, intervalIntegral.integral_const_mul, moment, raw, center, difference, foreign, macroRadius, epsilon, first, second, changed,
      prepared.referenceIdentity] using momentHistory.2.2 time inside
  have dilationBound' : dilation time ≤ 7 * bound ^ 2 * history := by
    apply le_trans _ (compare dilationI (fun current member => (scalarBounds current member).2.1))
    simpa only [dilationUpper, dilation, moment, center, raw, difference, foreign, macroRadius, ownRadius, epsilon, omega,
      first, second, changed, one_mul, abs_div, abs_pow, sq_abs, prepared.referenceIdentity] using dilationPrimitive time inside
  have phaseBound' : phaseValue time ≤ 13 * bound ^ 2 * history := by
    apply le_trans _ (compare phaseI (fun current member => (scalarBounds current member).2.2.1))
    rw [show phaseValue time = |relativeCorrectedPaperPhase (phaseCorrection 1 graph) phaseLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| from congrArg abs (phaseEquality inside)]
    apply ((phasePrimitive time inside).2).trans_eq
    apply intervalIntegral.integral_congr
    intro current _
    dsimp only [phaseUpper, dilation, moment, center, raw, difference, foreign, macroRadius, ownRadius, epsilon, omega, shape, relative, first, second, changed]
    simp only [one_mul, one_add_one_eq_two, Prod.fst_sub, Prod.snd_sub, abs_div, abs_pow, sq_abs, prepared.referenceIdentity]
  have translationBound : translation time ≤ 11 * bound ^ 2 * history := by
    apply le_trans _ (compare centerI (fun current member => (scalarBounds current member).2.2.2))
    simpa only [translation, centerUpper, moment, center, raw, external, foreign, ownRadius, epsilon, omega, first, second, changed, one_mul,
      prepared.referenceIdentity] using centerPrimitive time inside
  change size time ≤ shape time + 40 * bound ^ 2 * history
  rw [sizeIdentity]
  nlinarith only [dilationBound', phaseBound', momentBound, translationBound, mul_nonneg (sq_nonneg bound) historyNonnegative]

end EulerNonuniqueness.Paper

