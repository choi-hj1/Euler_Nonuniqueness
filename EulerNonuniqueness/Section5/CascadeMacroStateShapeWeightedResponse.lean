import EulerNonuniqueness.Section5.CascadeStrongNeutralLocalForeignWeightedReturn
import EulerNonuniqueness.Section5.CascadeCenterLocalForeignWeightedReturn
import EulerNonuniqueness.Section5.CascadeMacroStateWeightedLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeSelectedForeignForcingContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem macro_shape_scalar
    {bound weight omega strain epsilon ratio neutralConstant rawConstant momentConstant centerConstant macroConstant
      centered raw moment translation macroValue shape block macroPatch ownPatch physicalPatch external forcing : ℝ}
    (boundOne : 1 ≤ bound) (weightOne : 1 ≤ weight) (omegaNonnegative : 0 ≤ omega) (omegaWeight : omega ≤ weight)
    (strainNonnegative : 0 ≤ strain) (strainOne : strain ≤ 1)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (ratioOne : ratio ≤ 1)
    (neutralNonnegative : 0 ≤ neutralConstant) (neutralBelow : neutralConstant ≤ bound)
    (rawNonnegative : 0 ≤ rawConstant) (rawBelow : rawConstant ≤ bound)
    (momentNonnegative : 0 ≤ momentConstant) (momentBelow : momentConstant ≤ bound)
    (centerNonnegative : 0 ≤ centerConstant) (centerBelow : centerConstant ≤ bound)
    (macroNonnegative : 0 ≤ macroConstant) (macroBelow : macroConstant ≤ bound)
    (centeredNonnegative : 0 ≤ centered) (rawValueNonnegative : 0 ≤ raw) (momentValueNonnegative : 0 ≤ moment)
    (shapeNonnegative : 0 ≤ shape) (blockNonnegative : 0 ≤ block) (macroPatchNonnegative : 0 ≤ macroPatch)
    (ownNonnegative : 0 ≤ ownPatch) (physicalNonnegative : 0 ≤ physicalPatch) (externalNonnegative : 0 ≤ external)
    (forcingBound : block + epsilon * macroPatch + epsilon * ownPatch + physicalPatch + external ≤ forcing)
    (neutralEstimate : centered ≤ neutralConstant * shape + (neutralConstant / weight) *
      (block + epsilon * macroPatch + epsilon * ownPatch + epsilon * physicalPatch))
    (rawEstimate : weight * raw ≤ rawConstant * omega * centered + rawConstant * physicalPatch)
    (momentEstimate : weight * moment ≤ 2 * momentConstant *
      (strain * centered + block + epsilon * (strain * raw + macroPatch)))
    (centerEstimate : weight * translation ≤ moment + centered + external +
      centerConstant * omega * ratio * epsilon * (centered + raw) + centerConstant * ratio * epsilon * ownPatch)
    (macroEstimate : weight * macroValue ≤ weight * translation +
      (4 * weight * ratio + macroConstant * omega) * centered + macroConstant * physicalPatch) :
    let auxiliary := (1 + bound) * (1 + 3 * bound)
    let constant := (auxiliary + 4 + bound) * bound + auxiliary + bound
    macroValue ≤ constant * shape + (constant / weight) * forcing := by
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have forcingNonnegative : 0 ≤ forcing := (by positivity : 0 ≤ block + epsilon * macroPatch + epsilon * ownPatch + physicalPatch + external).trans forcingBound
  have physicalBound : physicalPatch ≤ forcing := by
    nlinarith only [forcingBound, blockNonnegative, externalNonnegative,
      mul_nonneg epsilonNonnegative macroPatchNonnegative, mul_nonneg epsilonNonnegative ownNonnegative]
  have macroBound : block + epsilon * macroPatch ≤ forcing := by
    nlinarith only [forcingBound, physicalNonnegative, externalNonnegative, mul_nonneg epsilonNonnegative ownNonnegative]
  have ownBound : epsilon * ownPatch ≤ forcing := by
    nlinarith only [forcingBound, blockNonnegative, physicalNonnegative, externalNonnegative,
      mul_nonneg epsilonNonnegative macroPatchNonnegative]
  have externalBound : external ≤ forcing := by
    nlinarith only [forcingBound, blockNonnegative, physicalNonnegative,
      mul_nonneg epsilonNonnegative macroPatchNonnegative, mul_nonneg epsilonNonnegative ownNonnegative]
  have neutralForcing : block + epsilon * macroPatch + epsilon * ownPatch + epsilon * physicalPatch ≤ forcing := by
    have physical := mul_le_of_le_one_left physicalNonnegative epsilonOne
    linarith only [forcingBound, physical, externalNonnegative]
  have neutral : centered ≤ bound * shape + (bound / weight) * forcing := by
    apply neutralEstimate.trans
    exact add_le_add (mul_le_mul_of_nonneg_right neutralBelow shapeNonnegative)
      ((mul_le_mul_of_nonneg_left neutralForcing (div_nonneg neutralNonnegative weightPositive.le)).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right neutralBelow weightPositive.le) forcingNonnegative))
  have rawUpper : weight * raw ≤ bound * weight * centered + bound * forcing := by
    exact rawEstimate.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul rawBelow omegaWeight omegaNonnegative boundNonnegative) centeredNonnegative)
      ((mul_le_mul_of_nonneg_left physicalBound rawNonnegative).trans (mul_le_mul_of_nonneg_right rawBelow forcingNonnegative)))
  have rawBound : raw ≤ bound * centered + (bound / weight) * forcing := by
    apply (mul_le_mul_left weightPositive).mp
    convert rawUpper using 1; field_simp [weightPositive.ne']; ring
  have epsilonStrain : epsilon * strain ≤ 1 := by
    nlinarith only [mul_le_mul epsilonOne strainOne strainNonnegative (by norm_num : (0 : ℝ) ≤ 1)]
  have momentForcing : strain * centered + block + epsilon * (strain * raw + macroPatch) ≤ centered + raw + forcing := by
    have first := mul_le_of_le_one_left centeredNonnegative strainOne
    have second := mul_le_of_le_one_left rawValueNonnegative epsilonStrain
    nlinarith only [first, second, macroBound]
  have momentUpper : weight * moment ≤ 2 * bound * (centered + raw + forcing) :=
    momentEstimate.trans ((mul_le_mul_of_nonneg_left momentForcing (by positivity : 0 ≤ 2 * momentConstant)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [momentBelow] : 2 * momentConstant ≤ 2 * bound) (by positivity)))
  have momentBound : moment ≤ 2 * bound * (centered + raw) + (2 * bound / weight) * forcing := by
    have localTerm := mul_le_mul_of_nonneg_right weightOne (show 0 ≤ 2 * bound * (centered + raw) by positivity)
    apply (mul_le_mul_left weightPositive).mp
    have comparison : 2 * bound * (centered + raw + forcing) ≤
        (2 * bound * (centered + raw) + (2 * bound / weight) * forcing) * weight := by
      field_simp [weightPositive.ne']
      nlinarith only [localTerm]
    convert momentUpper.trans comparison using 1; ring
  have centerFeedback : centerConstant * omega * ratio * epsilon ≤ bound * weight := by
    calc
      _ ≤ centerConstant * omega * 1 * 1 := by gcongr
      _ = centerConstant * omega := by ring
      _ ≤ bound * weight := mul_le_mul centerBelow omegaWeight omegaNonnegative boundNonnegative
  have centerOwn : centerConstant * ratio * epsilon * ownPatch ≤ bound * forcing := by
    have constantBound : centerConstant * ratio ≤ bound :=
      (mul_le_of_le_one_right centerNonnegative ratioOne).trans centerBelow
    have first := mul_le_mul_of_nonneg_right constantBound (mul_nonneg epsilonNonnegative ownNonnegative)
    have second := mul_le_mul_of_nonneg_left ownBound boundNonnegative
    nlinarith only [first, second]
  have centerUpper : weight * translation ≤ moment + centered + forcing +
      bound * weight * (centered + raw) + bound * forcing :=
    centerEstimate.trans (by
      have first := mul_le_mul_of_nonneg_right centerFeedback (add_nonneg centeredNonnegative rawValueNonnegative)
      linarith only [first, centerOwn, externalBound])
  have translationBound : translation ≤ moment + (1 + bound) * (centered + raw) + ((1 + bound) / weight) * forcing := by
    have localTerm := mul_le_mul_of_nonneg_right weightOne (show 0 ≤ moment + centered + raw by positivity)
    apply (mul_le_mul_left weightPositive).mp
    apply centerUpper.trans
    field_simp [weightPositive.ne']
    nlinarith only [localTerm, rawValueNonnegative]
  have macroUpper : weight * macroValue ≤ weight * translation + (4 + bound) * weight * centered + bound * forcing := by
    have first := mul_le_mul_of_nonneg_left ratioOne (show 0 ≤ 4 * weight by positivity)
    have second := mul_le_mul macroBelow omegaWeight omegaNonnegative boundNonnegative
    have third := mul_le_mul_of_nonneg_left physicalBound macroNonnegative
    have fourth := mul_le_mul_of_nonneg_right macroBelow forcingNonnegative
    nlinarith only [macroEstimate, first, second, third, fourth,
      mul_le_mul_of_nonneg_right (add_le_add first second) centeredNonnegative]
  have macroBound : macroValue ≤ translation + (4 + bound) * centered + (bound / weight) * forcing := by
    apply (mul_le_mul_left weightPositive).mp
    convert macroUpper using 1; field_simp [weightPositive.ne']; ring
  dsimp only
  let auxiliary := (1 + bound) * (1 + 3 * bound)
  have auxiliaryNonnegative : 0 ≤ auxiliary := by dsimp only [auxiliary]; positivity
  have translationSubstituted : translation ≤ auxiliary * centered + (auxiliary / weight) * forcing := by
    apply translationBound.trans
    apply (add_le_add_right (add_le_add_right momentBound _) _).trans
    have substituted := mul_le_mul_of_nonneg_left (add_le_add_left rawBound centered)
      (show 0 ≤ 2 * bound + (1 + bound) by positivity)
    convert add_le_add_right substituted (((2 * bound + (1 + bound)) / weight) * forcing) using 1 <;>
      dsimp only [auxiliary] <;> ring
  have combined : macroValue ≤ (auxiliary + 4 + bound) * centered + ((auxiliary + bound) / weight) * forcing := by
    have actual := macroBound.trans (add_le_add_right (add_le_add_right translationSubstituted _) _)
    convert actual using 1; ring
  have substituted := combined.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left neutral (show 0 ≤ auxiliary + 4 + bound by positivity)) _)
  have shapeComparison := mul_le_mul_of_nonneg_right (show (auxiliary + 4 + bound) * bound ≤
      (auxiliary + 4 + bound) * bound + auxiliary + bound by linarith only [auxiliaryNonnegative, boundNonnegative]) shapeNonnegative
  apply substituted.trans
  convert add_le_add_right shapeComparison
    ((((auxiliary + 4 + bound) * bound + auxiliary + bound) / weight) * forcing) using 1; ring

theorem exists_uniform_actual_macro_state_shape_weighted_response
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha → ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant boundaryConstant : ℝ},
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    let changed : Scales := {scales with frequency := frequency}
    let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let shape := fun time =>
      |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|
    let forcing := prepared.selectedForeignForcing (Finset.univ.erase index) index
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time index) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time index) ≤
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time) +
      (constant / weight) * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, neutralCap, neutralPositive, neutrals⟩ :=
    exists_uniform_actual_strong_neutral_local_foreign_weighted_return graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨momentCap, momentPositive, moments⟩ := exists_uniform_actual_firstMoment_local_foreign_weighted_return
  obtain ⟨centerCap, centerPositive, centers⟩ := exists_uniform_actual_center_local_foreign_weighted_return
  obtain ⟨rawSourceCap, rawSourcePositive, raws⟩ := exists_uniform_actual_raw_source_weighted_local_foreign_return
  obtain ⟨macroCap, macroPositive, macros⟩ := exists_uniform_actual_macro_state_weighted_local_foreign_return
  obtain ⟨partitionCap, partitionPositive, partitions⟩ := exists_uniform_actual_foreign_forcing_partition
  obtain ⟨regularRadius, regularPositive, _, regularity⟩ := exists_uniform_cascade_paired_chart_regularity graphAnalytic.contDiffAt coordinateSmooth
  let rawCap := min neutralCap (min momentCap (min centerCap (min rawSourceCap (min macroCap partitionCap))))
  have rawPositive : 0 < rawCap := lt_min neutralPositive (lt_min momentPositive (lt_min centerPositive (lt_min rawSourcePositive (lt_min macroPositive partitionPositive))))
  have neutralCapBound : rawCap ≤ neutralCap := min_le_left _ _
  have momentCapBound : rawCap ≤ momentCap := (min_le_right _ _).trans (min_le_left _ _)
  have centerCapBound : rawCap ≤ centerCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have rawCapBound : rawCap ≤ rawSourceCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have macroCapBound : rawCap ≤ macroCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have partitionCapBound : rawCap ≤ partitionCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨neutralRadius, neutralRadiusPositive, neutralQuarter, neutralConstant, neutralNonnegative, neutralRoot, neutralEight, neutralFactory⟩ :=
    neutrals factor factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, momentFactory⟩ := moments factorPositive factorEighth
  obtain ⟨centerConstant, centerNonnegative, centerFactory⟩ := centers factorPositive factorSmall
  obtain ⟨rawConstant, rawNonnegative, rawRoot, rawEight, rawFactory⟩ := raws factor factorPositive factorOne
  obtain ⟨macroConstant, macroNonnegative, macroRoot, macroEight, macroFactory⟩ := macros factor factorPositive factorOne
  let bound := 1 + neutralConstant + rawConstant + momentConstant + centerConstant + macroConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  let auxiliary := (1 + bound) * (1 + 3 * bound)
  let constant := (auxiliary + 4 + bound) * bound + auxiliary + bound
  have auxiliaryNonnegative : 0 ≤ auxiliary := by dsimp only [auxiliary]; positivity
  have constantOne : 1 ≤ constant := by
    have boundBelow : bound ≤ constant := by dsimp only [constant]; nlinarith only [auxiliaryNonnegative, boundNonnegative]
    exact boundOne.trans boundBelow
  let radius := min neutralRadius (regularRadius / 2)
  let rootMin := max neutralRoot (max rawRoot macroRoot)
  refine ⟨radius, lt_min neutralRadiusPositive (half_pos regularPositive), (min_le_left _ _).trans neutralQuarter,
    constant, constantOne, rootMin, neutralEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans ((neutralEight.trans (le_max_left _ _)).trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [neutralFactory scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      thresholdBound referenceNonnegative boundaryOne,
    momentFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    centerFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    rawFactory scales scaleRoot (((le_max_left _ _).trans (le_max_right _ _)).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant boundaryConstant thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    macroFactory scales scaleRoot (((le_max_right _ _).trans (le_max_right _ _)).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant boundaryConstant thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    partitions scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative regularPositive,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency neutralEstimate momentEstimate centerEstimate rawEstimate macroEstimate partitionEstimate selectedContinuous referenceSmall radii lengths strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let weight := 2 * Real.sqrt 2 * omega
  let location := changed.location (index.val + 1)
  let length := changed.length (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let ratio := length / location
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * length
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let shape := fun time =>
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).1 - (referenceStraightenedShape second.patchMotion graph coordinate index time).1| +
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).2 - (referenceStraightenedShape second.patchMotion graph coordinate index time).2|
  let centered := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
  let translation := fun time => ‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location
  let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first.patchMotion index time macroRadius power -
    quadrupoleExteriorCoefficient changed second.patchMotion index time macroRadius power‖
  let foreign := fun radius patch time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index) (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index) (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
  let external := fun patch time => ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
    biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖
  let forcing := prepared.selectedForeignForcing (Finset.univ.erase index) index
  have centerCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have macroCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have selectedCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have forcingCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have referenceCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).reference = prepared.reference := rfl
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have omegaWeight : omega ≤ weight := by dsimp only [weight]; nlinarith only [mul_le_mul_of_nonneg_right sqrtOne omegaPositive.le, omegaPositive]
  have weightOne : 1 ≤ weight := omegaOne.trans omegaWeight
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have epsilonOne : epsilon ≤ 1 := (div_le_one (sq_pos_of_pos lengthPositive)).mpr
    (pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (by simpa only [one_mul] using (radii (index.val + 1)).le) 2)
  have ratioOne : ratio ≤ 1 := (div_le_one locationPositive).mpr (by simpa only [one_mul] using (lengths (index.val + 1)).le)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := by
    have bothSmall : ∀ side, ∀ time ∈ Icc 0 finish,
        |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
          |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < regularRadius := by
      intro side time inside
      fin_cases side
      · exact (small time inside).trans_lt ((min_le_right _ _).trans_lt (half_lt_self regularPositive))
      · have sharp := referenceSmall prepared.toCascadeMaterialPreparedPair time ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
        change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < regularRadius
        linarith only [sharp, abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
    have regular := (regularity prepared.toCascadeMaterialPreparedPair path index finish finishBound bothSmall).1
    simpa only [shape, first, second, prepared.referenceIdentity, Prod.fst_sub, Prod.snd_sub] using regular.fst.abs.add regular.snd.abs
  have neutralData := neutralEstimate count phase dipoleAngle (prepared.enlargeCap neutralCapBound) path index nonterminal finish
    finishNonnegative finishBound radialSmall (fun time inside => (small time inside).trans (min_le_left _ _))
  have momentData := momentEstimate count phase dipoleAngle (prepared.enlargeCap momentCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall
  have centerData := centerEstimate count phase dipoleAngle (prepared.enlargeCap centerCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall weight weightPositive
  have rawData := rawEstimate count phase dipoleAngle (prepared.enlargeCap rawCapBound) path index finish finishNonnegative finishBound weight omegaWeight
  have macroData := macroEstimate count phase dipoleAngle (prepared.enlargeCap macroCapBound) path index finish finishNonnegative finishBound weight omegaWeight
  dsimp only at neutralData momentData centerData rawData macroData
  simp only [centerCapInvariant, rawCapInvariant, macroCapInvariant, referenceCapInvariant, prepared.referenceIdentity] at neutralData momentData centerData rawData macroData
  have differenceI : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish := momentData.1
  have macroPatchI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign macroRadius patch time) volume 0 finish := momentData.2.1 patch
  have ownPatchI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign ownRadius patch time) volume 0 finish := centerData.2.2.1 patch
  have physicalPatchI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign (changed.radius (index.val + 1)) patch time) volume 0 finish := by
    simpa only [foreign, first, second, norm_sub_rev] using rawData.1 patch
  have externalI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * external patch time) volume 0 finish := centerData.2.1 patch
  have shapeI : IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish :=
    ((by fun_prop : Continuous (fun time : ℝ => Real.exp (-weight * time))).continuousOn.mul shapeContinuous).intervalIntegrable_of_Icc finishNonnegative
  have selectedData := selectedContinuous count phase dipoleAngle prepared path index (Finset.univ.erase index) (by rfl)
  have forcingI : IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish :=
    ((by fun_prop : Continuous (fun time : ℝ => Real.exp (-weight * time))).continuousOn.mul
      (selectedData.2.1.mono (Icc_subset_Icc le_rfl finishBound))).intervalIntegrable_of_Icc finishNonnegative
  have sumI (values : Fin 4 → ℝ → ℝ)
      (integrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * values patch time) volume 0 finish) :
      IntervalIntegrable (fun time => Real.exp (-weight * time) * ∑ patch : Fin 4, values patch time) volume 0 finish := by
    simpa only [Finset.mul_sum] using (IntervalIntegrable.sum Finset.univ (fun patch _ => integrable patch))
  have sumIdentity (values : Fin 4 → ℝ → ℝ)
      (integrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * values patch time) volume 0 finish) :
      weighted (fun time => ∑ patch : Fin 4, values patch time) = ∑ patch : Fin 4, weighted (values patch) := by
    dsimp only [weighted]
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => integrable patch)
  let core := fun time => difference time + epsilon * (∑ patch : Fin 4, foreign macroRadius patch time) +
    epsilon * (∑ patch : Fin 4, foreign ownRadius patch time) +
    (∑ patch : Fin 4, foreign (changed.radius (index.val + 1)) patch time) +
    (∑ patch : Fin 4, external patch time) / (4 * location)
  have expandedCoreI := (((differenceI.add ((sumI _ macroPatchI).const_mul epsilon)).add
    ((sumI _ ownPatchI).const_mul epsilon)).add (sumI _ physicalPatchI)).add ((sumI _ externalI).div_const (4 * location))
  have coreI : IntervalIntegrable (fun time => Real.exp (-weight * time) * core time) volume 0 finish := by
    convert expandedCoreI using 1
    funext time
    dsimp only [core]
    ring
  have coreBound (time : ℝ) (inside : time ∈ Icc 0 finish) : core time ≤ forcing time := by
    let zeroDrive : Fin count := ⟨0, by omega⟩
    have actual := partitionEstimate count phase dipoleAngle (prepared.enlargeCap partitionCapBound) path
      ⟨inside.1, inside.2.trans finishBound⟩ index zeroDrive
    dsimp only at actual
    simp only [forcingCapInvariant, physicalCapInvariant, selectedCapInvariant] at actual
    have empty : Finset.univ.filter (fun source : Fin count => source.val < zeroDrive.val ∧ source ≠ index) = ∅ := by
      ext source; simp [zeroDrive]
    have allForeign : Finset.univ.filter (fun source : Fin count => zeroDrive.val ≤ source.val ∧ source ≠ index) = Finset.univ.erase index := by
      ext source; simp [zeroDrive, Finset.mem_erase, and_comm]
    rw [empty, allForeign] at actual
    have emptyForcing : prepared.selectedForeignForcing ∅ index time = 0 := by simp [CascadeSourcePreparedPair.selectedForeignForcing]
    have actualBound := actual.2.2
    rw [emptyForcing, zero_add] at actualBound
    change ‖quadrupoleRelativeLeadingStrain changed first.patchMotion second.patchMotion time index‖ +
      difference time + epsilon * (∑ patch : Fin 4, foreign macroRadius patch time) +
      epsilon * (∑ patch : Fin 4, foreign ownRadius patch time) +
      (∑ patch : Fin 4, external patch time) / (4 * location) +
      (∑ patch : Fin 4, foreign (changed.radius (index.val + 1)) patch time) ≤ forcing time at actualBound
    dsimp only [core]
    linarith only [actualBound, norm_nonneg (quadrupoleRelativeLeadingStrain changed first.patchMotion second.patchMotion time index)]
  have coreComparison := intervalIntegral.integral_mono_on finishNonnegative coreI forcingI
    (fun time inside => mul_le_mul_of_nonneg_left (coreBound time inside) (Real.exp_pos _).le)
  have coreIdentity : weighted core = weighted difference + epsilon * (∑ patch : Fin 4, weighted (foreign macroRadius patch)) +
      epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) +
      (∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch)) +
      (∑ patch : Fin 4, weighted (external patch)) / (4 * location) := by
    have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * core time) =
        ∫ time in (0 : ℝ)..finish,
          (((Real.exp (-weight * time) * difference time + epsilon * (Real.exp (-weight * time) * ∑ patch, foreign macroRadius patch time)) +
          epsilon * (Real.exp (-weight * time) * ∑ patch, foreign ownRadius patch time)) +
          Real.exp (-weight * time) * (∑ patch, foreign (changed.radius (index.val + 1)) patch time)) +
          (Real.exp (-weight * time) * ∑ patch, external patch time) / (4 * location) := by
      apply intervalIntegral.integral_congr
      intro time _
      dsimp only [core]
      ring
    change (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * core time) = _
    rw [identity, intervalIntegral.integral_add (((differenceI.add ((sumI _ macroPatchI).const_mul epsilon)).add
      ((sumI _ ownPatchI).const_mul epsilon)).add (sumI _ physicalPatchI)) ((sumI _ externalI).div_const (4 * location)),
      intervalIntegral.integral_add ((differenceI.add ((sumI _ macroPatchI).const_mul epsilon)).add ((sumI _ ownPatchI).const_mul epsilon)) (sumI _ physicalPatchI),
      intervalIntegral.integral_add (differenceI.add ((sumI _ macroPatchI).const_mul epsilon)) ((sumI _ ownPatchI).const_mul epsilon),
      intervalIntegral.integral_add differenceI ((sumI _ macroPatchI).const_mul epsilon),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    change weighted difference + epsilon * weighted (fun time => ∑ patch, foreign macroRadius patch time) +
      epsilon * weighted (fun time => ∑ patch, foreign ownRadius patch time) +
      weighted (fun time => ∑ patch, foreign (changed.radius (index.val + 1)) patch time) +
      weighted (fun time => ∑ patch, external patch time) / (4 * location) = _
    rw [sumIdentity _ macroPatchI, sumIdentity _ ownPatchI, sumIdentity _ physicalPatchI, sumIdentity _ externalI]
  change weighted core ≤ weighted forcing at coreComparison
  rw [coreIdentity] at coreComparison
  have weightedNonnegative (function : ℝ → ℝ) (nonnegative : ∀ time, 0 ≤ function time) : 0 ≤ weighted function :=
    intervalIntegral.integral_nonneg_of_forall finishNonnegative (fun time => mul_nonneg (Real.exp_pos _).le (nonnegative time))
  have foreignNonnegative (radius : ℝ) (patch : Fin 4) (time : ℝ) : 0 ≤ foreign radius patch time :=
    tsum_nonneg (fun power => mul_nonneg (by positivity) (norm_nonneg _))
  have rawNonnegativeActual (time : ℝ) : 0 ≤ raw time := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have centeredNonnegative (time : ℝ) : 0 ≤ centered time := div_nonneg (norm_nonneg _) lengthPositive.le
  have patchActionNonnegative (radius : ℝ) : 0 ≤ ∑ patch : Fin 4, weighted (foreign radius patch) :=
    Finset.sum_nonneg (fun patch _ => weightedNonnegative _ (foreignNonnegative radius patch))
  have actualNeutral : weighted centered ≤ neutralConstant * weighted shape + (neutralConstant / weight) *
      (weighted difference + epsilon * (∑ patch : Fin 4, weighted (foreign macroRadius patch)) +
        epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) +
        epsilon * (∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch))) := neutralData.2
  have actualRaw : weight * weighted raw ≤ rawConstant * omega * weighted centered +
      rawConstant * ∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch) := by
    simpa only [weighted, raw, centered, foreign, omega, first, second, norm_sub_rev] using rawData.2.2
  have actualMoment : weight * weighted moment ≤ 2 * momentConstant * (changed.strain * weighted centered + weighted difference +
      epsilon * (changed.strain * weighted raw + ∑ patch : Fin 4, weighted (foreign macroRadius patch))) := momentData.2.2.2.2.2
  have actualCenter : weight * weighted translation ≤ weighted moment + weighted centered +
      (∑ patch : Fin 4, weighted (external patch)) / (4 * location) + centerConstant * omega * ratio * epsilon * (weighted centered + weighted raw) +
      centerConstant * ratio * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch) := by
    simpa only [one_mul, weighted, moment, centered, raw, translation, foreign, external, ratio, omega, first, second] using centerData.2.2.2
  have actualMacro : weight * weighted (fun time => prepared.macroSourceState time index) ≤ weight * weighted translation +
      (4 * weight * ratio + macroConstant * omega) * weighted centered +
      macroConstant * ∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch) := by
    simpa only [weighted, translation, centered, foreign, ratio, omega, first, second, norm_sub_rev, div_eq_mul_inv, mul_assoc] using macroData.2.2
  refine ⟨macroData.2.1, shapeI, forcingI, ?_⟩
  have final := macro_shape_scalar boundOne weightOne omegaPositive.le omegaWeight strainNonnegative strainSmall.le
    epsilonNonnegative epsilonOne ratioOne neutralNonnegative (by dsimp only [bound]; linarith)
    rawNonnegative (by dsimp only [bound]; linarith) momentNonnegative (by dsimp only [bound]; linarith)
    centerNonnegative (by dsimp only [bound]; linarith) macroNonnegative (by dsimp only [bound]; linarith)
    (weightedNonnegative _ centeredNonnegative) (weightedNonnegative _ rawNonnegativeActual)
    (weightedNonnegative _ (fun time => norm_nonneg _))
    (weightedNonnegative _ (fun time => by dsimp only [shape]; positivity))
    (weightedNonnegative _ (fun time => tsum_nonneg (fun power => norm_nonneg _)))
    (patchActionNonnegative macroRadius) (patchActionNonnegative ownRadius) (patchActionNonnegative (changed.radius (index.val + 1)))
    (div_nonneg (Finset.sum_nonneg (fun patch _ => weightedNonnegative _ (fun time => norm_nonneg _))) (by positivity))
    coreComparison actualNeutral actualRaw actualMoment actualCenter actualMacro
  exact final

end EulerNonuniqueness.Paper
