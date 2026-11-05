import EulerNonuniqueness.General.FiniteStateCoefficientMajorants
import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence
import EulerNonuniqueness.Section5.CascadeForeignForcingPartition
import EulerNonuniqueness.Section1.UniformReferenceIndexBudget

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_coefficient_majorants
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ rawCap > (0 : ℝ), ∀ chartConstant ≥ (1 : ℝ),
    ∀ stableConstant ≥ (0 : ℝ), ∀ dilationConstant ≥ (0 : ℝ),
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    0 < tolerance → tolerance ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {cap shapeRadius monitor : ℝ}, cap ≤ rawCap →
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
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
    let omega := changed.omega (index.val + 1)
    let length := changed.length (index.val + 1)
    let macroRadius := factor / 39321600 * changed.location (index.val + 1)
    let ownRadius := factor / 39321600 * length
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    ∀ time ∈ Icc 0 finish,
    let relative := referenceStraightenedShape first graph coordinate index time - referenceStraightenedShape second graph coordinate index time
    let shape := |relative.1| + |relative.2|
    let moment := ‖relativeNormalizedFirstMoment changed first second index time‖
    let center := prepared.rawSourceCenteredState time index
    let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
    let leading := quadrupoleRelativeLeadingStrain changed first second time index
    let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
      quadrupoleExteriorCoefficient changed second index time macroRadius power‖
    let firstFamily := prepared.trajectory.movingFamily
    let secondFamily := prepared.referenceWitness.trajectory.movingFamily
    let foreign := fun receiverRadius patch => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid firstFamily.patchMotion current index patch) receiverRadius (power + 1) time -
        secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid secondFamily.patchMotion current index patch) receiverRadius (power + 1) time‖
    let dilationMajorant := tolerance * moment +
      (tolerance + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * center +
      dilationConstant * omega * epsilon * raw + dilationConstant * difference +
      dilationConstant * epsilon * ∑ patch : Fin 4, foreign ownRadius patch
    let forcing := |leading.2| + tolerance * (moment + center + shape) +
      stableConstant * omega * epsilon * (center + raw) + stableConstant * epsilon * ∑ patch : Fin 4, foreign ownRadius patch +
      stableConstant * (length / macroRadius) * (changed.strain * center + difference) + stableConstant * referenceSize * ‖leading‖
    let budget := omega * (prepared.finiteCoordinateSize graph coordinate suppliedLift index time + epsilon * raw) +
      prepared.selectedForeignForcing (Finset.univ.erase index) index time
    0 ≤ dilationMajorant ∧ dilationMajorant ≤ constant * budget ∧ 0 ≤ forcing ∧ forcing ≤ constant * budget := by
  obtain ⟨rawCap, capPositive, partitions⟩ := exists_uniform_actual_foreign_forcing_partition
  obtain ⟨radius, radiusPositive, radiusQuarter, geometryConstant, geometryOne, geometry⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨rawCap, capPositive, ?_⟩
  intro chartConstant chartOne stableConstant stableNonnegative dilationConstant dilationNonnegative
  let bound := 1 + geometryConstant + stableConstant + dilationConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith only [geometryOne, stableNonnegative, dilationNonnegative]
  have geometryBound : geometryConstant ≤ bound := by dsimp only [bound]; linarith only [stableNonnegative, dilationNonnegative]
  have stableBound : stableConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, dilationNonnegative]
  have dilationBound : dilationConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne, stableNonnegative]
  refine ⟨radius, radiusPositive, radiusQuarter, 10 * bound ^ 2, by nlinarith only [boundOne, sq_nonneg (bound - 1)], ?_⟩
  intro factor factorPositive factorSmall scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    scaleRoot boundaryConstant threshold referenceConstant tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive toleranceOne
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [geometry scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive factorEighth thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    partitions scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_uniform_reference_index_budget_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (show (0 : ℝ) < factor / 39321600 by positivity),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)] with frequency geometryEstimate coherence partitionEstimate referenceBudget lengths radii strainSmall frequencyOne
  intro count phase dipoleAngle cap shapeRadius monitor capBound prepared path index nonterminal finish finishNonnegative finishBound small
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  dsimp only
  obtain ⟨lift, liftContinuous, liftPolar, _, _, _, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound small
  have liftEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusQuarter) lift suppliedLift
    (fun side => (liftContinuous side).1.continuousOn) suppliedContinuous
    (fun side => (liftContinuous side).2.trans (suppliedInitial side).symm) liftPolar suppliedPolar).2.2 graph coordinate
  intro time inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  let macroRadius := factor / 39321600 * changed.location (index.val + 1)
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let relative := referenceStraightenedShape first graph coordinate index time - referenceStraightenedShape second graph coordinate index time
  let shape := |relative.1| + |relative.2|
  let moment := ‖relativeNormalizedFirstMoment changed first second index time‖
  let center := prepared.rawSourceCenteredState time index
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let leading := quadrupoleRelativeLeadingStrain changed first second time index
  let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time macroRadius power - quadrupoleExteriorCoefficient changed second index time macroRadius power‖
  let foreign := fun receiverRadius patch => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch) receiverRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch) receiverRadius (power + 1) time‖
  let own := ∑ patch : Fin 4, foreign ownRadius patch
  let macroForeign := ∑ patch : Fin 4, foreign macroRadius patch
  let external := (∑ patch : Fin 4, ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
    biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * changed.location (index.val + 1))
  let size := prepared.finiteCoordinateSize graph coordinate suppliedLift index time
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive : 0 < changed.location (index.val + 1) := changed.location_pos _
  have macroPositive : 0 < macroRadius := mul_pos (div_pos factorPositive (by norm_num)) locationPositive
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonOne : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (by simpa only [one_mul] using (radii (index.val + 1)).le) 2
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have macroRatioNonnegative : 0 ≤ length / macroRadius := div_nonneg lengthPositive.le macroPositive.le
  have macroRatioOne : length / macroRadius ≤ 1 := (div_le_one macroPositive).mpr (lengths (index.val + 1)).le
  have referenceNonnegative' : 0 ≤ referenceSize := (referenceBudget (index.val + 1)).1
  have referenceOne : referenceSize ≤ 1 := (referenceBudget (index.val + 1)).2.le
  have shapeNonnegative : 0 ≤ shape := by dsimp only [shape]; positivity
  have momentNonnegative : 0 ≤ moment := norm_nonneg _
  have sizeParts : size = shape +
      (|diagonalDifference first time index - diagonalDifference second time index| / length ^ 2 +
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| +
        ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1)) + moment := by
    dsimp only [size, shape, relative, CascadeSourcePreparedPair.finiteCoordinateSize, first, second, changed, length, Prod.fst_sub, Prod.snd_sub]
    ring
  have extraNonnegative : 0 ≤ size - shape - moment := by
    have actual : 0 ≤ |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2 +
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| +
        ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1) :=
      add_nonneg (add_nonneg (div_nonneg (abs_nonneg _) (sq_nonneg _)) (abs_nonneg _))
        (div_nonneg (norm_nonneg _) locationPositive.le)
    convert actual using 1
    rw [sizeParts]
    ring
  have shapeSize : shape ≤ size := by linarith only [extraNonnegative, momentNonnegative]
  have momentSize : moment ≤ size := by linarith only [extraNonnegative, shapeNonnegative]
  have sizeNonnegative : 0 ≤ size := shapeNonnegative.trans shapeSize
  have centerNonnegative : 0 ≤ center := div_nonneg (norm_nonneg _) lengthPositive.le
  have centerBound := (geometryBounds time inside).1
  rw [liftEquality inside] at centerBound
  have centerSize : center ≤ bound * size := centerBound.trans (mul_le_mul_of_nonneg_right geometryBound sizeNonnegative)
  have rawNonnegative : 0 ≤ raw := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have differenceNonnegative : 0 ≤ difference := tsum_nonneg fun _ => norm_nonneg _
  have foreignNonnegative (receiverRadius : ℝ) : 0 ≤ ∑ patch : Fin 4, foreign receiverRadius patch := by
    exact Finset.sum_nonneg (fun _ _ => tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _)))
  have externalNonnegative : 0 ≤ external := div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (by norm_num) locationPositive.le)
  have componentBound : |leading.2| ≤ ‖leading‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le leading
  have forcingIdentity : prepared.finiteCoordinateForeignForcing index time =
      ‖leading‖ + difference + epsilon * macroForeign + epsilon * own + external := by
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateForeignForcing, leading, difference, epsilon, macroForeign, own, external, foreign, first, second, changed, length, macroRadius, ownRadius]
    rw [prepared.referenceIdentity]
  let zeroDrive : Fin count := ⟨0, by omega⟩
  have partition := partitionEstimate count phase dipoleAngle (prepared.enlargeCap capBound) path
    ⟨inside.1, inside.2.trans finishBound⟩ index zeroDrive
  dsimp only at partition
  have empty : Finset.univ.filter (fun source : Fin count => source.val < zeroDrive.val ∧ source ≠ index) = ∅ := by ext source; simp [zeroDrive]
  have allForeign : Finset.univ.filter (fun source : Fin count => zeroDrive.val ≤ source.val ∧ source ≠ index) = Finset.univ.erase index := by
    ext source; simp [zeroDrive, Finset.mem_erase, and_comm]
  have fullBound := partition.2.2
  rw [empty, allForeign] at fullBound
  change prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time ≤
    prepared.selectedForeignForcing ∅ index time + prepared.selectedForeignForcing (Finset.univ.erase index) index time at fullBound
  have emptyForcing : prepared.selectedForeignForcing ∅ index time = 0 := by simp [CascadeSourcePreparedPair.selectedForeignForcing]
  rw [emptyForcing, zero_add] at fullBound
  have physicalNonnegative := prepared.physicalForeignSourceForcing_nonneg index time
  have forcingBound : ‖leading‖ + difference + epsilon * macroForeign + epsilon * own + external ≤
      prepared.selectedForeignForcing (Finset.univ.erase index) index time := by rw [← forcingIdentity]; linarith only [fullBound, physicalNonnegative]
  have scalar := General.finite_state_coefficient_majorants boundOne omegaOne epsilonNonnegative epsilonOne
    strainNonnegative strainSmall.le macroRatioNonnegative macroRatioOne referenceNonnegative' referenceOne tolerancePositive.le toleranceOne
    shapeNonnegative shapeSize momentNonnegative momentSize centerNonnegative centerSize rawNonnegative (abs_nonneg _) componentBound
    differenceNonnegative (foreignNonnegative ownRadius) (foreignNonnegative macroRadius) externalNonnegative stableNonnegative stableBound dilationNonnegative dilationBound
  dsimp only at scalar
  have budgetNonnegative : 0 ≤ omega * (size + epsilon * raw) + (‖leading‖ + difference + epsilon * macroForeign + epsilon * own + external) :=
    add_nonneg (mul_nonneg (zero_le_one.trans omegaOne) (add_nonneg sizeNonnegative (mul_nonneg epsilonNonnegative rawNonnegative)))
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) differenceNonnegative)
        (mul_nonneg epsilonNonnegative (foreignNonnegative macroRadius)))
        (mul_nonneg epsilonNonnegative (foreignNonnegative ownRadius))) externalNonnegative)
  have budgetBound := add_le_add_left forcingBound (omega * (size + epsilon * raw))
  have sevenTen := mul_le_mul_of_nonneg_right (show 7 * bound ^ 2 ≤ 10 * bound ^ 2 by nlinarith only [sq_nonneg bound]) budgetNonnegative
  have tenBound := mul_le_mul_of_nonneg_left budgetBound (show 0 ≤ 10 * bound ^ 2 by positivity)
  exact ⟨scalar.1, scalar.2.1.trans (sevenTen.trans tenBound), scalar.2.2.1, scalar.2.2.2.trans tenBound⟩

end EulerNonuniqueness.Paper
