import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryEvolution
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryCapRefinement
import EulerNonuniqueness.Section3.CanonicalExteriorCommonObservableContinuity
import EulerNonuniqueness.Section3.CanonicalExteriorCoefficientPairContinuity
import EulerNonuniqueness.General.QuadraticNeutralInteriorHistory

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.General EulerNonuniqueness.Section6 FiniteMovingPatchFamily

local instance actualCommonBoundaryHistoryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem exists_uniform_actual_common_boundary_original_time_history :
    ∃ constant ≥ (1 : ℝ), ∃ rawCap > 0, ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ radiusCoefficient ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {requestedCap shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      0 < requestedCap → requestedCap ≤ rawCap →
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (index : Fin count) (patch : Fin 4),
      let changed : Scales := {scales with frequency := frequency}
      let label := finProdFinEquiv (index, patch)
      let signedFrequency := patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4
      let radius := radiusCoefficient / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)
      let distance := fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance label signedFrequency current radius
        (prepared.referenceWitness.trajectory.spectralCoordinate label current) (prepared.trajectory.spectralCoordinate label current)
      let coefficients := canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily label label
      ∀ time ∈ Icc 0 path.stop,
        distance time ≤ constant * distance 0 +
          ∫ current in (0 : ℝ)..time, constant * coefficients current + constant * |signedFrequency| * radius ^ 2 * distance current ∧
        distance time ≤ Real.exp (constant * |signedFrequency| * radius ^ 2 * time) *
          (constant * distance 0 + ∫ current in (0 : ℝ)..time,
            Real.exp (-(constant * |signedFrequency| * radius ^ 2) * current) * (constant * coefficients current)) := by
  classical
  obtain ⟨caps, pointConstant, pointOne, points⟩ := exists_canonical_common_boundary_forcing_rate
  obtain ⟨odePhysical, odePhysicalPositive, odeSpectral, odeSpectralPositive, observableEquations⟩ :=
    canonicalExteriorCommonPhysicalCoordinate_exists_joint_observable_evolution_ball
  obtain ⟨continuousRaw, continuousRawPositive, continuousPhysical, continuousPhysicalPositive,
    continuousSpectral, continuousSpectralPositive, observableContinuity⟩ :=
    canonicalExteriorCommonCoordinates_exists_geometric_continuity_ball
  let refined := caps.refinePhysicalSpectral (min odePhysical continuousPhysical) (min odeSpectral continuousSpectral)
    (lt_min odePhysicalPositive continuousPhysicalPositive) (lt_min odeSpectralPositive continuousSpectralPositive)
  obtain ⟨evolutionCap, evolutionCapPositive, evolutionParameters⟩ := exists_uniform_actual_common_boundary_evolution refined
  obtain ⟨recordCap, recordCapPositive, recordParameters⟩ := exists_uniform_actual_common_boundary_record refined
  obtain ⟨shapeCap, shapeCapPositive, shapes⟩ := exists_actual_source_stopped_shape_radius_monotone caps.rawPositive
  let rawCap := min continuousRaw (min evolutionCap (min recordCap shapeCap))
  let groupBound := diskPhysicalGroupBound + 1
  let groupScale := (groupBound + 1) * groupBound
  let constant := groupScale * pointConstant
  have groupOne : 1 ≤ groupBound := by dsimp only [groupBound]; linarith [diskPhysicalGroupBound_nonnegative]
  have groupNonnegative : 0 ≤ groupBound := zero_le_one.trans groupOne
  have groupScaleOne : 1 ≤ groupScale := by dsimp only [groupScale]; nlinarith only [groupOne]
  have constantOne : 1 ≤ constant := by dsimp only [constant]; nlinarith only [groupScaleOne, pointOne]
  have groupScaleLe : groupScale ≤ constant := by
    dsimp only [constant]
    exact le_mul_of_one_le_right (zero_le_one.trans groupScaleOne) pointOne
  refine ⟨constant, constantOne, rawCap, lt_min continuousRawPositive
    (lt_min evolutionCapPositive (lt_min recordCapPositive shapeCapPositive)), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨coefficient, coefficientOne, evolutionRoot, evolutionEight, evolutionBounds⟩ := evolutionParameters factor factorPositive factorSmall
  obtain ⟨closedCoefficient, _, recordRoot, recordEight, recordBounds⟩ := recordParameters factor factorPositive factorSmall
  obtain ⟨materialRoot, materialEight, materialBounds⟩ := exists_uniform_actual_common_boundary_material_envelopes factor factorPositive factorSmall
  let rootMin := max evolutionRoot (max recordRoot materialRoot)
  refine ⟨coefficient, coefficientOne, rootMin, evolutionEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [evolutionBounds scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    recordBounds scales scaleRoot ((le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    materialBounds scales scaleRoot ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative] with frequency evolution record material
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path index patch
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let label := finProdFinEquiv (index, patch)
  let signedFrequency := patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4
  let radius := coefficient / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)
  let firstDistance := changed.length (index.val + 1) / 400
  let finalDistance := factor * changed.length (index.val + 1) / 400
  let firstFamily := prepared.referenceWitness.trajectory.movingFamily
  let finalFamily := prepared.trajectory.movingFamily
  let firstRaw := prepared.referenceWitness.trajectory.spectralCoordinate label
  let finalRaw := prepared.trajectory.spectralCoordinate label
  let firstShape := fun current => (prepared.referenceWitness.trajectory.curve current).2.2 label
  let finalShape := fun current => (prepared.trajectory.curve current).2.2 label
  let firstQ := fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate label signedFrequency current (diskPhysicalSpectralChart (firstRaw current))
  let finalQ := fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate label signedFrequency current (diskPhysicalSpectralChart (finalRaw current))
  let firstEta := fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate label signedFrequency current (diskPhysicalSpectralChart (firstRaw current))
  let finalEta := fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate label signedFrequency current (diskPhysicalSpectralChart (finalRaw current))
  let coefficients := canonicalExteriorCoefficientPairSeries firstFamily finalFamily label label
  have evolutionActual := by
    with_reducible_and_instances
      exact evolution count orbit sectionTime phase dipoleAngle prepared requestedPositive
        (requestedSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) path
  have recordActual := by
    with_reducible_and_instances
      exact record count orbit sectionTime phase dipoleAngle prepared requestedPositive
        (requestedSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) path
  have reconstruction (current : ℝ) (inside : current ∈ Icc 0 path.stop) :
      diskPhysicalSpectralChart (firstRaw current) = firstShape current ∧ diskPhysicalSpectralChart (finalRaw current) = finalShape current := by
    obtain ⟨first, final⟩ := shapes prepared
      (requestedSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) path current inside label
    exact ⟨first.reconstruct, final.reconstruct⟩
  have firstShapeContinuous : Continuous firstShape :=
    (continuous_apply label).comp (continuous_snd.comp (continuous_snd.comp prepared.referenceWitness.trajectory.continuous))
  have finalShapeContinuous : Continuous finalShape :=
    (continuous_apply label).comp (continuous_snd.comp (continuous_snd.comp prepared.trajectory.continuous))
  have continuityAt (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      ContinuousAt (fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate label signedFrequency current (firstShape current)) time ∧
      ContinuousAt (fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate label signedFrequency current (firstShape current)) time ∧
      ContinuousAt (fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate label signedFrequency current (finalShape current)) time ∧
      ContinuousAt (fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate label signedFrequency current (finalShape current)) time ∧
      ContinuousAt coefficients time := by
    have comparison := by
      with_reducible_and_instances
        exact recordActual time inside index patch
    obtain ⟨firstScale, finalScale, firstNear, finalNear⟩ := material count orbit sectionTime phase dipoleAngle
      prepared.toCascadeMaterialPreparedPair path time inside index patch
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
    have sourceInside (source : Fin (count * 4)) (_ : source ∈ Finset.univ.erase label) :
        time ∈ Ioo (firstFamily.patch source).initialTime (firstFamily.patch source).finalTime := by
      change time ∈ Ioo (-(1 : ℝ)) 3
      exact globalInside
    have finalSourceInside (source : Fin (count * 4)) (_ : source ∈ Finset.univ.erase label) :
        time ∈ Ioo (finalFamily.patch source).initialTime (finalFamily.patch source).finalTime := by
      change time ∈ Ioo (-(1 : ℝ)) 3
      exact globalInside
    have shapeBounds := prepared.raw_shape_caps requestedPositive path inside label
    have rawSmall : requestedCap ≤ continuousRaw := requestedSmall.trans (min_le_left _ _)
    have identities := reconstruction time inside
    have firstPhysical := comparison.firstPhysical.trans ((min_le_right _ _).trans (min_le_right _ _))
    have finalPhysical := comparison.finalPhysical.trans ((min_le_right _ _).trans (min_le_right _ _))
    have firstSpectral := comparison.firstSpectral.trans ((min_le_right _ _).trans (min_le_right _ _))
    have finalSpectral := comparison.finalSpectral.trans ((min_le_right _ _).trans (min_le_right _ _))
    with_reducible_and_instances
      change ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate label signedFrequency time (diskPhysicalSpectralChart (firstRaw time)) - standardCircleBanach‖ ≤ continuousPhysical at firstPhysical
      change ‖firstFamily.canonicalExteriorCommonPhysicalCoordinate label signedFrequency time (diskPhysicalSpectralChart (finalRaw time)) - standardCircleBanach‖ ≤ continuousPhysical at finalPhysical
      change ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate label signedFrequency time (diskPhysicalSpectralChart (firstRaw time))‖ ≤ continuousSpectral at firstSpectral
      change ‖firstFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate label signedFrequency time (diskPhysicalSpectralChart (finalRaw time))‖ ≤ continuousSpectral at finalSpectral
    rw [identities.1] at firstPhysical firstSpectral
    rw [identities.2] at finalPhysical finalSpectral
    have firstContinuity := observableContinuity firstFamily label firstShape
      (frequency := signedFrequency) (time := time) (distance := firstDistance)
      (weight := changed.referenceLocalExteriorWeight (index.val + 1)) firstShapeContinuous.continuousAt
      (shapeBounds.1.le.trans rawSmall) comparison.frequencyNonzero comparison.firstPositive comparison.weightNonnegative firstScale
      sourceInside firstNear.self_of_nhds.1 (firstNear.mono fun _ actual => actual.2.1)
      firstPhysical firstSpectral
    have finalContinuity := observableContinuity firstFamily label finalShape
      (frequency := signedFrequency) (time := time) (distance := firstDistance)
      (weight := changed.referenceLocalExteriorWeight (index.val + 1)) finalShapeContinuous.continuousAt
      (shapeBounds.2.le.trans rawSmall) comparison.frequencyNonzero comparison.firstPositive comparison.weightNonnegative firstScale
      sourceInside firstNear.self_of_nhds.1 (firstNear.mono fun _ actual => actual.2.1)
      finalPhysical finalSpectral
    have finalWeightNonnegative : 0 ≤ changed.cascadeLocalExteriorWeight factor (index.val + 1) :=
      (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans finalNear.self_of_nhds.2.1
    have coefficientContinuity := firstFamily.canonicalExteriorCoefficientPairSeries_continuousAt_geometric finalFamily label label
      (time := time) (firstDistance := firstDistance) (finalDistance := finalDistance)
      (firstWeight := changed.referenceLocalExteriorWeight (index.val + 1))
      (finalWeight := changed.cascadeLocalExteriorWeight factor (index.val + 1))
      comparison.firstPositive comparison.finalPositive comparison.weightNonnegative finalWeightNonnegative firstScale finalScale
      sourceInside finalSourceInside firstNear.self_of_nhds.1 finalNear.self_of_nhds.1
      (firstNear.mono fun _ actual => actual.2.1) (finalNear.mono fun _ actual => actual.2.1)
    exact ⟨firstContinuity.1, firstContinuity.2, finalContinuity.1, finalContinuity.2, coefficientContinuity⟩
  have firstQContinuous : ContinuousOn firstQ (Icc 0 path.stop) := by
    apply (show ContinuousOn (fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate label signedFrequency current (firstShape current)) (Icc 0 path.stop) from
      fun time inside => (continuityAt time inside).1.continuousWithinAt).congr
    intro time inside
    dsimp only [firstQ]
    rw [(reconstruction time inside).1]
  have finalQContinuous : ContinuousOn finalQ (Icc 0 path.stop) := by
    apply (show ContinuousOn (fun current => firstFamily.canonicalExteriorCommonQuadraticCoordinate label signedFrequency current (finalShape current)) (Icc 0 path.stop) from
      fun time inside => (continuityAt time inside).2.2.1.continuousWithinAt).congr
    intro time inside
    dsimp only [finalQ]
    rw [(reconstruction time inside).2]
  have firstEtaContinuous : ContinuousOn firstEta (Icc 0 path.stop) := by
    apply (show ContinuousOn (fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate label signedFrequency current (firstShape current)) (Icc 0 path.stop) from
      fun time inside => (continuityAt time inside).2.1.continuousWithinAt).congr
    intro time inside
    dsimp only [firstEta]
    rw [(reconstruction time inside).1]
  have finalEtaContinuous : ContinuousOn finalEta (Icc 0 path.stop) := by
    apply (show ContinuousOn (fun current => firstFamily.canonicalExteriorCommonTrueAngularCoordinate label signedFrequency current (finalShape current)) (Icc 0 path.stop) from
      fun time inside => (continuityAt time inside).2.2.2.1.continuousWithinAt).congr
    intro time inside
    dsimp only [finalEta]
    rw [(reconstruction time inside).2]
  have coefficientContinuous : ContinuousOn coefficients (Icc 0 path.stop) := fun time inside => (continuityAt time inside).2.2.2.2.continuousWithinAt
  let comparisons := fun time (inside : time ∈ Ioo 0 path.stop) => Classical.choose (evolutionActual time inside index patch)
  let firstResidual := fun time => if inside : time ∈ Ioo 0 path.stop then (comparisons time inside).firstResidual else 0
  let finalResidual := fun time => if inside : time ∈ Ioo 0 path.stop then (comparisons time inside).finalResidual else 0
  let sourceDifference := fun time => if inside : time ∈ Ioo 0 path.stop then (comparisons time inside).sourceDifference else 0
  let firstQForce := fun time => firstFamily.canonicalExteriorCommonQuadraticMaterialForcing label signedFrequency time (diskPhysicalSpectralChart (firstRaw time)) (firstResidual time) 0
  let finalQForce := fun time => firstFamily.canonicalExteriorCommonQuadraticMaterialForcing label signedFrequency time (diskPhysicalSpectralChart (finalRaw time)) (finalResidual time) (sourceDifference time)
  let firstEtaForce := fun time => firstFamily.canonicalExteriorCommonTrueAngularForcing label signedFrequency time (diskPhysicalSpectralChart (firstRaw time)) (firstResidual time) 0
  let finalEtaForce := fun time => firstFamily.canonicalExteriorCommonTrueAngularForcing label signedFrequency time (diskPhysicalSpectralChart (finalRaw time)) (finalResidual time) (sourceDifference time)
  have actualEquations (time : ℝ) (inside : time ∈ Ioo 0 path.stop) :
      HasDerivAt firstQ ((signedFrequency • diskRotatingDerivative) (firstQ time) + firstQForce time) time ∧
      HasDerivAt firstEta (firstEtaForce time) time ∧
      HasDerivAt finalQ ((signedFrequency • diskRotatingDerivative) (finalQ time) + finalQForce time) time ∧
      HasDerivAt finalEta (finalEtaForce time) time := by
    have actual : CanonicalCommonBoundaryEvolutionAt (comparisons time inside) firstRaw finalRaw := by
      with_reducible_and_instances
        exact Classical.choose_spec (evolutionActual time inside index patch)
    have comparison := comparisons time inside
    have firstEquation := actual.firstEquation
    have first := by
      with_reducible_and_instances
        exact observableEquations firstFamily label (fun current => diskPhysicalSpectralChart (firstRaw current))
          (frequency := signedFrequency) (time := time)
          comparison.firstResidual 0 (comparison.firstPhysical.trans ((min_le_right _ _).trans (min_le_left _ _)))
          (comparison.firstSpectral.trans ((min_le_right _ _).trans (min_le_left _ _)))
          (by simpa only [map_zero, add_zero] using firstEquation)
    have final := by
      with_reducible_and_instances
        exact observableEquations firstFamily label (fun current => diskPhysicalSpectralChart (finalRaw current))
          (frequency := signedFrequency) (time := time)
          comparison.finalResidual comparison.sourceDifference (comparison.finalPhysical.trans ((min_le_right _ _).trans (min_le_left _ _)))
          (comparison.finalSpectral.trans ((min_le_right _ _).trans (min_le_left _ _))) actual.finalEquation
    have result := And.intro first.1 (And.intro first.2 (And.intro final.1 final.2))
    with_reducible_and_instances
      simpa only [firstQ, firstEta, finalQ, finalEta, firstQForce, firstEtaForce, finalQForce, finalEtaForce,
        firstResidual, finalResidual, sourceDifference, dif_pos inside] using result
  have forcingBound (time : ℝ) (inside : time ∈ Ioo 0 path.stop) :
      ‖finalQForce time - firstQForce time‖ + radius * ‖finalEtaForce time - firstEtaForce time‖ ≤
      pointConstant * |signedFrequency| * radius ^ 2 * weightedBoundaryPairDistance radius (firstQ time) (finalQ time) (firstEta time) (finalEta time) +
        pointConstant * coefficients time := by
    have comparison := comparisons time inside
    have actual := by
      with_reducible_and_instances
        exact points firstFamily finalFamily label label signedFrequency time firstDistance finalDistance
          (changed.referenceLocalExteriorWeight (index.val + 1)) (2 * changed.circulation (index.val + 1)) radius (firstRaw time) (finalRaw time)
          comparison.of_refinePhysicalSpectral
    have firstResidualIdentity : comparison.of_refinePhysicalSpectral.firstResidual = comparison.firstResidual := rfl
    have finalResidualIdentity : comparison.of_refinePhysicalSpectral.finalResidual = comparison.finalResidual := rfl
    have sourceIdentity : comparison.of_refinePhysicalSpectral.sourceDifference = comparison.sourceDifference := rfl
    with_reducible_and_instances rw [firstResidualIdentity, finalResidualIdentity, sourceIdentity] at actual
    with_reducible_and_instances
      simpa only [firstQForce, finalQForce, firstEtaForce, finalEtaForce, firstResidual, finalResidual, sourceDifference, dif_pos inside,
        CanonicalCommonBoundaryPairAt.boundaryDistance, CanonicalCommonBoundaryPairAt.coefficientDifferenceSeries,
        firstQ, finalQ, firstEta, finalEta, coefficients, canonicalExteriorCoefficientPairSeries, mul_add, mul_assoc] using actual
  have radiusNonnegative : 0 ≤ radius := (comparisons (path.stop / 2) ⟨by linarith [path.stopPositive], by linarith [path.stopPositive]⟩).radiusNonnegative
  have groupZero : diskPhysicalScaledGroup signedFrequency 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    simpa only [diskPhysicalScaledGroup, mul_zero] using diskPhysicalGroup_zero
  have groupAddition (first final : ℝ) : diskPhysicalScaledGroup signedFrequency (first + final) =
      (diskPhysicalScaledGroup signedFrequency first).comp (diskPhysicalScaledGroup signedFrequency final) := by
    simpa only [diskPhysicalScaledGroup, mul_add] using diskPhysicalGroup_add (signedFrequency * first) (signedFrequency * final)
  have groupEstimate (time : ℝ) (value : PeriodicC1HolderHalf) : ‖diskPhysicalScaledGroup signedFrequency time value‖ ≤ groupBound * ‖value‖ :=
    (diskPhysicalScaledGroup_norm_bound signedFrequency time value).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [groupBound]; linarith) (norm_nonneg value))
  have history := quadraticNeutral_pair_history_without_forcing_continuity
    (source := fun current => pointConstant * coefficients current) (rate := pointConstant * |signedFrequency| * radius ^ 2)
    (diskPhysicalScaledGroup signedFrequency) (signedFrequency • diskRotatingDerivative) groupZero groupAddition
    (diskPhysicalScaledGroup_generator signedFrequency) groupOne groupEstimate radiusNonnegative (by positivity) path.stopPositive.le
    firstQContinuous finalQContinuous firstEtaContinuous finalEtaContinuous (continuousOn_const.mul coefficientContinuous)
    (fun time _ => mul_nonneg (zero_le_one.trans pointOne) (tsum_nonneg fun _ => by positivity))
    (fun time inside => (actualEquations time inside).1) (fun time inside => (actualEquations time inside).2.2.1)
    (fun time inside => (actualEquations time inside).2.1) (fun time inside => (actualEquations time inside).2.2.2) forcingBound
  intro time inside
  have bound := history time inside
  have initialNonnegative : 0 ≤ weightedBoundaryPairDistance radius (firstQ 0) (finalQ 0) (firstEta 0) (finalEta 0) := by
    unfold weightedBoundaryPairDistance
    positivity
  have initialBound := mul_le_mul_of_nonneg_right groupScaleLe initialNonnegative
  have integralResult := bound.1.trans (add_le_add_right initialBound _)
  have exponentialResult := bound.2.trans (mul_le_mul_of_nonneg_left (add_le_add_right initialBound _) (Real.exp_pos _).le)
  with_reducible_and_instances
    constructor
    · simpa only [canonicalExteriorCommonBoundaryDistance, firstQ, finalQ, firstEta, finalEta, firstRaw, finalRaw,
        firstFamily, finalFamily, coefficients, radius, signedFrequency, label, changed, constant, groupScale, mul_assoc] using integralResult
    · simpa only [canonicalExteriorCommonBoundaryDistance, firstQ, finalQ, firstEta, finalEta, firstRaw, finalRaw,
        firstFamily, finalFamily, coefficients, radius, signedFrequency, label, changed, constant, groupScale, mul_assoc] using exponentialResult

end EulerNonuniqueness.Paper
