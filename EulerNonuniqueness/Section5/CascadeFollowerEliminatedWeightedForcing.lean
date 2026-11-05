import EulerNonuniqueness.Section5.CascadeFollowerArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeMacroStateShapeArbitraryWeightResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem eliminated_selected_union_le
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (first second : Finset (Fin count)) (disjoint : Disjoint first second) (receiver : Fin count) (time : ℝ) :
    prepared.selectedForeignForcing (first ∪ second) receiver time ≤
      prepared.selectedForeignForcing first receiver time + prepared.selectedForeignForcing second receiver time := by
  have triangle := norm_add_le
    (∑ source ∈ first, relativeBlockSourceShapeInput scales prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver source time)
    (∑ source ∈ second, relativeBlockSourceShapeInput scales prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver source time)
  dsimp only [CascadeSourcePreparedPair.selectedForeignForcing]
  simp only [Finset.sum_union disjoint, Finset.sum_add_distrib]
  linear_combination triangle

private theorem eliminated_weighted_scale (function : ℝ → ℝ) (scalar weight finish : ℝ) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (scalar * function time)) =
      scalar * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro time _
  ring

theorem exists_uniform_actual_follower_eliminated_weighted_forcing
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ macroConstant ≥ (1 : ℝ),
    ∃ followerConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (4 * followerConstant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime tolerance : ℝ), 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time drive| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time drive| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time drive| ≤ radius) →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    ∀ weight : ℝ, ({scales with frequency := frequency} : Scales).omega (drive.val + 1) ≤ weight →
    let changed : Scales := {scales with frequency := frequency}
    let coarserSources := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
    let finerSources := Finset.univ.filter (fun source : Fin count => drive.val < source.val ∧ source ≠ drive)
    let allForcing := prepared.selectedForeignForcing (Finset.univ.erase drive) drive
    let coarserForcing := prepared.selectedForeignForcing coarserSources drive
    let finerForcing := prepared.selectedForeignForcing finerSources drive
    let remaining := prepared.followerStrictlyFinerForcing drive
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let shape := fun time =>
      |(referenceStraightenedShape first graph coordinate drive time).1 - (referenceStraightenedShape second graph coordinate drive time).1| +
      |(referenceStraightenedShape first graph coordinate drive time).2 - (referenceStraightenedShape second graph coordinate drive time).2|
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
    ContinuousOn allForcing (Icc 0 finish) ∧ ContinuousOn coarserForcing (Icc 0 finish) ∧
    ContinuousOn finerForcing (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time drive) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * allForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * coarserForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * finerForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * remaining time) volume 0 finish ∧
    (∀ time ∈ Icc 0 finish, prepared.finiteCoordinateForeignForcing drive time +
      prepared.physicalForeignSourceForcing drive time ≤ allForcing time) ∧
    weighted allForcing ≤ 2 * macroConstant * tolerance * weighted shape + 2 * weighted finerForcing +
      (4 * followerConstant * rho / (changed.omega (drive.val + 1) * changed.location (drive.val + 1) ^ 4)) * weighted remaining := by
  obtain ⟨macroThreshold, macroThresholdPositive, macroThresholdEighth, macroCap, macroCapPositive, macroFactory⟩ :=
    exists_uniform_actual_macro_state_shape_arbitrary_weight_response graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨followerThreshold, followerThresholdPositive, _, followerCap, followerCapPositive, followerFactory⟩ :=
    exists_uniform_actual_follower_arbitrary_weight_return
  obtain ⟨partitionCap, partitionCapPositive, partitions⟩ := exists_uniform_actual_foreign_forcing_partition
  let thresholdMax := min macroThreshold followerThreshold
  let rawCap := min macroCap (min followerCap partitionCap)
  have macroCapBound : rawCap ≤ macroCap := min_le_left _ _
  have followerCapBound : rawCap ≤ followerCap := (min_le_right _ _).trans (min_le_left _ _)
  have partitionCapBound : rawCap ≤ partitionCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, lt_min macroThresholdPositive followerThresholdPositive,
    (min_le_left _ _).trans macroThresholdEighth, rawCap,
    lt_min macroCapPositive (lt_min followerCapPositive partitionCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨macroRadius, macroRadiusPositive, macroQuarter, macroConstant, macroOne, macroRoot, macroRootEight, macros⟩ :=
    macroFactory factor factorPositive factorSmall
  obtain ⟨followerRadius, followerRadiusPositive, _, followerConstant, followerOne, followerRoot, _, followers⟩ :=
    followerFactory factorPositive factorSmall
  let radius := min macroRadius followerRadius
  let rootMin := max macroRoot followerRoot
  refine ⟨radius, lt_min macroRadiusPositive followerRadiusPositive, (min_le_left _ _).trans macroQuarter,
    macroConstant, macroOne, followerConstant, followerOne, rootMin, macroRootEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime tolerance tolerancePositive
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans
    (macroRootEight.trans ((le_max_left _ _).trans rootLarge))
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans ((min_le_left _ _).trans macroThresholdEighth)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [macros scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative boundaryOne,
    followers scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant
      boundaryConstant (thresholdBound.trans (min_le_right _ _)) referenceNonnegative boundaryOne orbit sectionTime tolerance tolerancePositive,
    partitions scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive factorOne,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (max (1 : ℝ) (2 * macroConstant * tolerance))]
    with frequency macroEstimate followerEstimate partitionEstimate selectedContinuous frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path drive nonterminal finish finishNonnegative finishBound
    radialSmall targetSmall followerSmall weight omegaWeight
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (drive.val + 1)
  let location := changed.location (drive.val + 1)
  let coarserSources := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
  let finerSources := Finset.univ.filter (fun source : Fin count => drive.val < source.val ∧ source ≠ drive)
  let allForcing := prepared.selectedForeignForcing (Finset.univ.erase drive) drive
  let coarserForcing := prepared.selectedForeignForcing coarserSources drive
  let finerForcing := prepared.selectedForeignForcing finerSources drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let shape := fun time =>
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate drive time).1 -
      (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).1| +
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate drive time).2 -
      (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).2|
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  have macroCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have weightedCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext current source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroCapInvariant]
  have selectedCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have remainingCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have forcingCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have macroData := macroEstimate count phase dipoleAngle (prepared.enlargeCap macroCapBound) path drive nonterminal finish
    finishNonnegative finishBound radialSmall (fun time inside => (targetSmall time inside).trans (min_le_left _ _)) weight omegaWeight
  dsimp only at macroData
  simp only [macroCapInvariant, selectedCapInvariant] at macroData
  obtain ⟨macroI, shapeI, allI, macroBound⟩ := macroData
  have followerData := followerEstimate count phase dipoleAngle (prepared.enlargeCap followerCapBound) path drive nonterminal finish
    finishNonnegative finishBound (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_right _ _))
      weight omegaWeight
  dsimp only at followerData
  simp only [weightedCapInvariant, selectedCapInvariant, remainingCapInvariant] at followerData
  obtain ⟨_, _, remainingContinuous, _, _, _, _, _, _, _, _, remainingI, _, _, _, returnedBound⟩ := followerData
  have coarserSubset : coarserSources ⊆ Finset.univ.erase drive := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have finerSubset : finerSources ⊆ Finset.univ.erase drive := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have allData := selectedContinuous count phase dipoleAngle prepared path drive (Finset.univ.erase drive) (Finset.Subset.refl _)
  have coarserData := selectedContinuous count phase dipoleAngle prepared path drive coarserSources coarserSubset
  have finerData := selectedContinuous count phase dipoleAngle prepared path drive finerSources finerSubset
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have allContinuous : ContinuousOn allForcing (Icc 0 finish) := allData.2.1.mono subset
  have coarserContinuous : ContinuousOn coarserForcing (Icc 0 finish) := coarserData.2.1.mono subset
  have finerContinuous : ContinuousOn finerForcing (Icc 0 finish) := finerData.2.1.mono subset
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have coarserI := (weightContinuous.continuousOn.mul coarserContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have finerI := (weightContinuous.continuousOn.mul finerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaOne : 1 ≤ omega := frequencyOne.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have weightPositive : 0 < weight := omegaPositive.trans_le omegaWeight
  have locationPositive : 0 < location := changed.location_pos _
  have locationFourth : 0 < location ^ 4 := pow_pos locationPositive _
  have disjoint : Disjoint coarserSources finerSources := Finset.disjoint_left.mpr (by
    intro source coarser finer
    have below := (Finset.mem_filter.mp coarser).2.1
    have above := (Finset.mem_filter.mp finer).2.1
    omega)
  have unionIdentity : coarserSources ∪ finerSources = Finset.univ.erase drive := by
    ext source
    simp only [coarserSources, finerSources, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (⟨_, different⟩ | ⟨_, different⟩) <;> exact different
    · intro different
      by_cases below : source.val < drive.val
      · exact Or.inl ⟨below, different⟩
      · have valuesDifferent : source.val ≠ drive.val := fun equality => different (Fin.ext equality)
        exact Or.inr ⟨by omega, different⟩
  have allBound (time : ℝ) : allForcing time ≤ coarserForcing time + finerForcing time := by
    have actual := eliminated_selected_union_le prepared coarserSources finerSources disjoint drive time
    rwa [unionIdentity] at actual
  have partitionAction : weighted allForcing ≤ weighted coarserForcing + weighted finerForcing := by
    have actual := intervalIntegral.integral_mono_on finishNonnegative allI (coarserI.add finerI) (by
      intro time _
      have comparison := mul_le_mul_of_nonneg_left (allBound time) (Real.exp_pos (-weight * time)).le
      convert comparison using 1; ring)
    rwa [intervalIntegral.integral_add coarserI finerI] at actual
  have normalizedReturn : location ^ 4 * weighted coarserForcing ≤
      tolerance * (location ^ 4 * weighted (fun time => prepared.macroSourceState time drive)) +
        (2 * followerConstant * rho / omega) * weighted remaining := by
    change (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (location ^ 4 * coarserForcing time)) ≤
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (location ^ 4 * prepared.macroSourceState time drive)) +
        (2 * followerConstant * rho / omega) * weighted remaining at returnedBound
    simpa only [eliminated_weighted_scale] using returnedBound
  have followerBound : weighted coarserForcing ≤
      tolerance * weighted (fun time => prepared.macroSourceState time drive) +
        (2 * followerConstant * rho / (omega * location ^ 4)) * weighted remaining := by
    apply (mul_le_mul_left locationFourth).mp
    calc
      _ ≤ _ := normalizedReturn
      _ = _ := by field_simp; ring
  have actualMacroBound : weighted (fun time => prepared.macroSourceState time drive) ≤
      macroConstant * weighted shape + (macroConstant / weight) * weighted allForcing := macroBound
  have allActionNonnegative : 0 ≤ weighted allForcing := intervalIntegral.integral_nonneg_of_forall finishNonnegative
    (fun time => mul_nonneg (Real.exp_pos _).le (allData.1 time))
  have feedbackSmall : tolerance * (macroConstant / weight) ≤ (1 / 2 : ℝ) := by
    have frequencyBound : 2 * macroConstant * tolerance ≤ frequency := (le_max_right _ _).trans frequencyLarge
    have frequencyOmega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) (drive.val + 1)
    have weightBound : 2 * macroConstant * tolerance ≤ weight := frequencyBound.trans (frequencyOmega.trans omegaWeight)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ weightPositive).mpr
    nlinarith only [weightBound]
  have scaledMacro := mul_le_mul_of_nonneg_left actualMacroBound tolerancePositive.le
  have feedback := mul_le_mul_of_nonneg_right feedbackSmall allActionNonnegative
  have eliminated : weighted allForcing ≤ 2 * macroConstant * tolerance * weighted shape + 2 * weighted finerForcing +
      (4 * followerConstant * rho / (omega * location ^ 4)) * weighted remaining := by
    have coefficientIdentity : 4 * followerConstant * rho / (omega * location ^ 4) =
        2 * (2 * followerConstant * rho / (omega * location ^ 4)) := by ring
    rw [coefficientIdentity]
    nlinarith only [partitionAction, followerBound, scaledMacro, feedback]
  have literalBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateForeignForcing drive time + prepared.physicalForeignSourceForcing drive time ≤ allForcing time := by
    let zeroDrive : Fin count := ⟨0, by omega⟩
    have actual := partitionEstimate count phase dipoleAngle (prepared.enlargeCap partitionCapBound) path
      ⟨inside.1, inside.2.trans finishBound⟩ drive zeroDrive
    dsimp only at actual
    simp only [forcingCapInvariant, physicalCapInvariant, selectedCapInvariant] at actual
    have empty : Finset.univ.filter (fun source : Fin count => source.val < zeroDrive.val ∧ source ≠ drive) = ∅ := by
      ext source
      simp [zeroDrive]
    have allForeign : Finset.univ.filter (fun source : Fin count => zeroDrive.val ≤ source.val ∧ source ≠ drive) = Finset.univ.erase drive := by
      ext source
      simp [zeroDrive, Finset.mem_erase, and_comm]
    rw [empty, allForeign] at actual
    have emptyForcing : prepared.selectedForeignForcing ∅ drive time = 0 := by
      simp [CascadeSourcePreparedPair.selectedForeignForcing]
    have bound := actual.2.2
    rwa [emptyForcing, zero_add] at bound
  exact ⟨allContinuous, coarserContinuous, finerContinuous, remainingContinuous, macroI, shapeI, allI,
    coarserI, finerI, remainingI, literalBound, eliminated⟩

end EulerNonuniqueness.Paper
