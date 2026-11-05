import EulerNonuniqueness.General.FiniteStateAdditiveMajorant
import EulerNonuniqueness.Section1.UniformNonlinearRadiusSmallness
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget
import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence
import EulerNonuniqueness.Section6.PaperActualRelativeStrainForcing

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_additive_smallness
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ), ∃ toleranceMax > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 8 →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant threshold referenceConstant chartConstant tolerance : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    0 ≤ chartConstant → 0 ≤ tolerance → tolerance ≤ toleranceMax →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {cap : ℝ} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
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
    let dilation := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
    let leading := quadrupoleRelativeLeadingStrain changed first second time index
    let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
      quadrupoleExteriorCoefficient changed second index time macroRadius power‖
    let foreign := ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first current index patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
          ownRadius (power + 1) time‖
    let additive := tolerance * (moment + center + shape) + stableConstant * omega * epsilon * (center + raw) +
      stableConstant * epsilon * foreign + stableConstant * (length / macroRadius) * (changed.strain * center + difference) +
      stableConstant * referenceSize * ‖leading‖ + stableConstant * omega * referenceSize * dilation
    0 ≤ additive ∧ additive ≤ accuracy *
      (prepared.finiteCoordinateSize graph coordinate suppliedLift index time + raw + foreign + difference + ‖leading‖) := by
  obtain ⟨radius, radiusPositive, radiusQuarter, geometryConstant, geometryOne, geometry⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro stableConstant stableNonnegative accuracy accuracyPositive
  let bound := 1 + geometryConstant + stableConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith only [geometryOne, stableNonnegative]
  have boundPositive : 0 < bound := zero_lt_one.trans_le boundOne
  have geometryBound : geometryConstant ≤ bound := by dsimp only [bound]; linarith only [stableNonnegative]
  have stableBound : stableConstant ≤ bound := by dsimp only [bound]; linarith only [geometryOne]
  let smallness := accuracy / (6 * bound ^ 2)
  have smallnessPositive : 0 < smallness := by dsimp only [smallness]; positivity
  refine ⟨smallness, smallnessPositive, ?_⟩
  intro factor factorPositive factorSmall scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant threshold
    referenceConstant chartConstant tolerance rootPositive boundaryNonnegative thresholdSmall referenceNonnegative chartNonnegative
    toleranceNonnegative toleranceSmall
  filter_upwards [geometry scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive factorSmall
      thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_uniform_omega_relative_patch_area_small amplitudePositive (by linarith only [ratioBound]) smallnessPositive,
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      (mul_nonneg chartNonnegative referenceNonnegative) smallnessPositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (show 0 < smallness * (factor / 39321600) by positivity),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)] with frequency geometryEstimate coherence areaSmall referenceSmall lengths strainSmall frequencyOne
  intro cap orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small suppliedLift suppliedContinuous suppliedInitial suppliedPolar
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
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let relative := referenceStraightenedShape first graph coordinate index time - referenceStraightenedShape second graph coordinate index time
  let shape := |relative.1| + |relative.2|
  let moment := ‖relativeNormalizedFirstMoment changed first second index time‖
  let center := prepared.rawSourceCenteredState time index
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let dilation := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
  let size := prepared.finiteCoordinateSize graph coordinate suppliedLift index time
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have macroPositive : 0 < macroRadius := mul_pos (div_pos factorPositive (by norm_num)) locationPositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have macroRatioSmall : length / macroRadius ≤ smallness := by
    apply (div_le_iff₀ macroPositive).mpr
    simpa only [macroRadius, mul_assoc] using (lengths (index.val + 1)).le
  have referenceNonnegative' : 0 ≤ referenceSize := by
    dsimp only [referenceSize]
    exact mul_nonneg (mul_nonneg chartNonnegative referenceNonnegative)
      (add_nonneg (div_nonneg (add_nonneg strainNonnegative (sq_nonneg _)) omegaPositive.le)
        (pow_nonneg (inv_nonneg.mpr omegaPositive.le) _))
  have shapeNonnegative : 0 ≤ shape := by dsimp only [shape]; positivity
  have momentNonnegative : 0 ≤ moment := norm_nonneg _
  have dilationNonnegative : 0 ≤ dilation := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have sizeParts : size = shape + dilation +
      |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| +
      moment + ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1) := by
    dsimp only [size, shape, dilation, relative, moment, CascadeSourcePreparedPair.finiteCoordinateSize, first, second, changed, length, Prod.fst_sub, Prod.snd_sub]
  have extraNonnegative : 0 ≤ size - shape - dilation - moment := by
    have actual := add_nonneg (abs_nonneg (relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift
      (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time))
      (div_nonneg (norm_nonneg (quadrupoleCenter first time index - quadrupoleCenter second time index)) locationPositive.le)
    convert actual using 1
    rw [sizeParts]
    ring
  have shapeSize : shape ≤ size := by linarith only [extraNonnegative, dilationNonnegative, momentNonnegative]
  have momentSize : moment ≤ size := by linarith only [extraNonnegative, dilationNonnegative, shapeNonnegative]
  have dilationSize : dilation ≤ size := by linarith only [extraNonnegative, shapeNonnegative, momentNonnegative]
  have centerNonnegative : 0 ≤ center := div_nonneg (norm_nonneg _) lengthPositive.le
  have centerBound := (geometryBounds time inside).1
  rw [liftEquality inside] at centerBound
  have centerSize : center ≤ bound * size := centerBound.trans
    (mul_le_mul_of_nonneg_right geometryBound (shapeNonnegative.trans shapeSize))
  have rawNonnegative : 0 ≤ raw := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have differenceNonnegative : 0 ≤ ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
      quadrupoleExteriorCoefficient changed second index time macroRadius power‖ := tsum_nonneg fun _ => norm_nonneg _
  have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first current index patch) (factor / 39321600 * length) (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
          (factor / 39321600 * length) (power + 1) time‖ :=
    Finset.sum_nonneg fun _ _ => tsum_nonneg fun _ => mul_nonneg (by positivity) (norm_nonneg _)
  have estimate := General.finite_state_additive_majorant boundOne omegaOne smallnessPositive.le
    (show 0 ≤ epsilon by dsimp only [epsilon]; positivity) (areaSmall (index.val + 1)).2.le
    strainNonnegative strainSmall.le (div_nonneg lengthPositive.le macroPositive.le) macroRatioSmall
    referenceNonnegative' (referenceSmall (index.val + 1)).2.le toleranceNonnegative toleranceSmall
    shapeNonnegative shapeSize momentNonnegative momentSize centerNonnegative centerSize dilationNonnegative dilationSize
    rawNonnegative (norm_nonneg (quadrupoleRelativeLeadingStrain changed first second time index))
    differenceNonnegative foreignNonnegative stableNonnegative stableBound
  have coefficientIdentity : 6 * bound ^ 2 * smallness = accuracy := by
    dsimp only [smallness]
    field_simp [boundPositive.ne']
  exact ⟨estimate.1, by simpa only [coefficientIdentity] using estimate.2⟩

end EulerNonuniqueness.Paper
