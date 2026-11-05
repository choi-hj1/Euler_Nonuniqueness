import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryShapeCaps
import EulerNonuniqueness.Section5.CascadeCommonBoundaryRawFinePair
import EulerNonuniqueness.Section5.CascadeCommonBoundaryMaterialEnvelopes
import EulerNonuniqueness.Section5.CascadeCommonBoundaryCapMonotonicity
import EulerNonuniqueness.General.QuarticCommonBoundaryNumericCaps

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.General EulerNonuniqueness.Section6
open FiniteMovingPatchFamily

local instance actualCommonBoundaryRecordC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem exists_uniform_actual_common_boundary_record (caps : CanonicalCommonBoundaryRateCaps) :
    ∃ rawCap > 0, ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
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
      ∀ time ∈ Icc 0 path.stop, ∀ (index : Fin count) (patch : Fin 4),
      let changed : Scales := {scales with frequency := frequency}
      let label := finProdFinEquiv (index, patch)
      let omega := changed.omega (index.val + 1)
      CanonicalCommonBoundaryPairAt caps prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
        label label (patchSign patch * changed.amplitude * omega ^ 4) time
        (changed.length (index.val + 1) / 400) (factor * changed.length (index.val + 1) / 400)
        (changed.referenceLocalExteriorWeight (index.val + 1)) (2 * changed.circulation (index.val + 1))
        (radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2))
        (prepared.referenceWitness.trajectory.spectralCoordinate label time)
        (prepared.trajectory.spectralCoordinate label time) := by
  obtain ⟨stateRadius, statePositive, forcingRadius, forcingPositive, forcingLe, shiftConstant, shiftOne, shapeCaps⟩ :=
    canonicalExteriorCommonRawSpectralCoordinate_exists_boundary_shape_caps caps
  obtain ⟨shapeCap, shapeCapPositive, shapes⟩ := exists_actual_source_stopped_shape_radius_monotone statePositive
  obtain ⟨fineCap, fineCapPositive, fineParameters⟩ := exists_uniform_actual_common_boundary_raw_fine_pair
  let rawCap := min shapeCap fineCap
  have rawPositive : 0 < rawCap := lt_min shapeCapPositive fineCapPositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨fineCoefficient, fineOne, fineRoot, fineEight, fineBounds⟩ := fineParameters factor factorPositive factorSmall
  obtain ⟨materialRoot, materialEight, materialBounds⟩ := exists_uniform_actual_common_boundary_material_envelopes factor factorPositive factorSmall
  obtain ⟨forcingConstant, forcingOne, scaleBounds⟩ := Scales.exists_uniform_reference_local_material_scale_bound
  let radiusCoefficient := max fineCoefficient (600 * (forcingConstant + 1))
  have coefficientLarge : 600 * (forcingConstant + 1) ≤ radiusCoefficient := le_max_right _ _
  have coefficientOne : 1 ≤ radiusCoefficient := fineOne.trans (le_max_left _ _)
  let mapCoefficient := (‖diskPhysicalTransverseProjection‖ + ‖diskNeutralCLM‖) * caps.mapConstant
  let shiftCoefficient := ‖diskPhysicalTransverseProjection‖ * shiftConstant
  have mapNonnegative : 0 ≤ mapCoefficient :=
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (zero_le_one.trans caps.mapOne)
  have shiftNonnegative : 0 ≤ shiftCoefficient := by dsimp only [shiftCoefficient]; positivity
  obtain ⟨numericRoot, numericEight, numericBounds⟩ := exists_uniform_quartic_common_boundary_numeric_caps
    forcingOne coefficientLarge mapNonnegative shiftNonnegative caps.quadraticOne forcingPositive caps.shapePositive
  let rootMin := max fineRoot (max materialRoot numericRoot)
  refine ⟨radiusCoefficient, coefficientOne, rootMin, fineEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  have rootFine : fineRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootMaterial : materialRoot ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
  have rootNumeric : numericRoot ≤ scaleRoot := (le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)
  have rootEight : 8 ≤ scaleRoot := fineEight.trans rootFine
  have rootPositive : 0 < scaleRoot := by linarith
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [fineBounds scales scaleRoot rootFine amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative,
    materialBounds scales scaleRoot rootMaterial amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative,
    eventually_ge_atTop (1 : ℝ),
    (scales.strain_tendsto_zero ratioLarge alphaPositive).eventually (eventually_lt_nhds zero_lt_one)]
    with frequency fine material frequencyOne strainSmall
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path time inside index patch
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let label := finProdFinEquiv (index, patch)
  let omega := changed.omega (index.val + 1)
  let signedFrequency := patchSign patch * changed.amplitude * omega ^ 4
  let radius := radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2)
  let weight := changed.referenceLocalExteriorWeight (index.val + 1)
  let mass := 2 * changed.circulation (index.val + 1)
  let firstDistance := changed.length (index.val + 1) / 400
  let finalDistance := factor * changed.length (index.val + 1) / 400
  let first := prepared.referenceWitness.trajectory.spectralCoordinate label time
  let final := prepared.trajectory.spectralCoordinate label time
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have omegaPositive : 0 < omega := by linarith
  have frequencyAbs : |signedFrequency| = scaleRoot ^ 3 * omega ^ 4 := by
    dsimp only [signedFrequency]
    rw [← Real.norm_eq_abs, norm_mul, norm_mul, norm_patchSign, one_mul,
      Real.norm_of_nonneg amplitudePositive.le, Real.norm_of_nonneg (by positivity : 0 ≤ omega ^ 4)]
    rw [show changed.amplitude = scaleRoot ^ 3 from amplitudeIdentity]
  have signedNonzero : signedFrequency ≠ 0 := abs_pos.mp (by rw [frequencyAbs]; positivity)
  have firstPositive : 0 < firstDistance := div_pos (changed.length_pos _) (by norm_num)
  have finalPositive : 0 < finalDistance := div_pos (mul_pos factorPositive (changed.length_pos _)) (by norm_num)
  have scalar := scaleBounds changed scaleRoot amplitudeIdentity rootEight frequencyOne ratioLarge strainSmall.le (index.val + 1)
  obtain ⟨radiusPositive, radiusOne, radiusSmall, epsilonForcing, epsilonSmall, squaredSmall, tailSmall,
    derivativeSmall, mapSmall, shiftSmall, quadraticSmall, _⟩ :=
    numericBounds scaleRoot rootNumeric omega weight mass firstDistance
      (changed.radius (index.val + 1) / firstDistance) omegaOne scalar.1 scalar.2.2.2.2.1 firstPositive scalar.2.2.1 scalar.2.1
      scalar.2.2.2.1 scalar.2.2.2.2.2
  rw [← frequencyAbs] at epsilonForcing epsilonSmall squaredSmall tailSmall derivativeSmall mapSmall shiftSmall
  have actualMaterial := material count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside index patch
  obtain ⟨firstScale, finalScale, firstNear, finalNear⟩ := actualMaterial
  have firstSeparated := prepared.referenceWitness.trajectory.movingFamily.exterior_domain_gap_of_center_gaps label firstNear.self_of_nhds.1
  have finalSeparated := prepared.trajectory.movingFamily.exterior_domain_gap_of_center_gaps label finalNear.self_of_nhds.1
  have weightBound := firstNear.self_of_nhds.2.1
  have massBound := firstNear.self_of_nhds.2.2
  obtain ⟨firstShape, finalShape⟩ := shapes prepared (requestedSmall.trans (min_le_left _ _)) path time inside label
  have firstReconstruct : diskPhysicalSpectralChart first = (prepared.referenceWitness.trajectory.curve time).2.2 label := firstShape.reconstruct
  have finalReconstruct : diskPhysicalSpectralChart final = (prepared.trajectory.curve time).2.2 label := finalShape.reconstruct
  have firstArea : diskSpectralTubularArea first = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart first) = Real.pi
    rw [firstReconstruct]
    exact firstShape.area
  have finalArea : diskSpectralTubularArea final = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart final) = Real.pi
    rw [finalReconstruct]
    exact finalShape.area
  have firstCentered : contourCentroidFunctional (diskPhysicalSpectralChart first) = 0 := by rw [firstReconstruct]; exact firstShape.centroid
  have finalCentered : contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 := by rw [finalReconstruct]; exact finalShape.centroid
  have firstInside : first ∈ ball 0 stateRadius := by simpa only [mem_ball, dist_zero_right] using firstShape.small
  have finalInside : final ∈ ball 0 stateRadius := by simpa only [mem_ball, dist_zero_right] using finalShape.small
  have firstShapeCaps := by
    with_reducible_and_instances
      exact shapeCaps prepared.referenceWitness.trajectory.movingFamily label first firstInside firstArea firstCentered
        (frequency := signedFrequency) (time := time) (distance := firstDistance) (weight := weight)
        signedNonzero firstPositive scalar.1 firstScale firstSeparated weightBound epsilonForcing
  obtain ⟨firstCaps, firstSmall, _, firstPhysical, firstSpectral, firstCorrectedArea, firstCorrectedBound⟩ := firstShapeCaps
  have finalShapeCaps := by
    with_reducible_and_instances
      exact shapeCaps prepared.referenceWitness.trajectory.movingFamily label final finalInside finalArea finalCentered
        (frequency := signedFrequency) (time := time) (distance := firstDistance) (weight := weight)
        signedNonzero firstPositive scalar.1 firstScale firstSeparated weightBound epsilonForcing
  obtain ⟨finalCaps, finalSmall, finalField, finalPhysical, finalSpectral, finalCorrectedArea, finalCorrectedBound⟩ := finalShapeCaps
  have fineActual := by
    with_reducible_and_instances
      exact fine count orbit sectionTime phase dipoleAngle prepared requestedPositive
        (requestedSmall.trans (min_le_right _ _)) path time inside index patch
  have fineRadius : fineCoefficient / (scaleRoot ^ 2 * omega ^ 2) ≤ radius :=
    div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have firstTransverse : ‖diskPhysicalTransverseProjection first‖ ≤ radius / 8 := by
    with_reducible_and_instances
      exact fineActual.1.le.trans (div_le_div_of_nonneg_right fineRadius (by norm_num))
  have finalTransverse : ‖diskPhysicalTransverseProjection final‖ ≤ radius / 8 := by
    with_reducible_and_instances
      exact fineActual.2.le.trans (div_le_div_of_nonneg_right fineRadius (by norm_num))
  have correctedCap {state : PeriodicC1HolderHalf}
      (raw : ‖diskPhysicalTransverseProjection state‖ ≤ radius / 8)
      (corrected : ‖diskPhysicalTransverseProjection
        (prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate label signedFrequency time (diskPhysicalSpectralChart state))‖ ≤
          ‖diskPhysicalTransverseProjection state‖ + ‖diskPhysicalTransverseProjection‖ * (shiftConstant * (weight / |signedFrequency|))) :
      ‖diskPhysicalTransverseProjection
        (prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonNormalizedPhysicalCoordinate label signedFrequency time (diskPhysicalSpectralChart state))‖ ≤ radius := by
    have shift : ‖diskPhysicalTransverseProjection‖ * (shiftConstant * (weight / |signedFrequency|)) ≤ radius / 8 := by
      simpa only [shiftCoefficient, mul_assoc] using shiftSmall
    linarith
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have firstMember : first ∈ contourContinuousVectorSubmodule := by
    simpa only [first, MovingCentroidGaugeTrajectory.spectralCoordinate] using firstShape.stateContinuousVector
  have finalMember : final ∈ contourContinuousVectorSubmodule := by
    simpa only [final, MovingCentroidGaugeTrajectory.spectralCoordinate] using finalShape.stateContinuousVector
  have materialInside : time ∈ Ioo (prepared.referenceWitness.trajectory.movingFamily.patch label).initialTime
      (prepared.referenceWitness.trajectory.movingFamily.patch label).finalTime := globalInside
  have eighthLe : radius / 8 ≤ radius := by linarith only [radiusPositive]
  with_reducible_and_instances refine {
    firstInside := firstCaps
    finalInside := finalCaps
    firstMember := firstMember
    finalMember := finalMember
    firstPhysicalMember := by rw [firstReconstruct]; exact firstShape.continuousVector
    finalPhysicalMember := by rw [finalReconstruct]; exact finalShape.continuousVector
    firstArea := firstArea
    finalArea := finalArea
    firstCentered := firstCentered
    finalCentered := finalCentered
    firstSmall := firstSmall
    finalSmall := finalSmall
    frequencyNonzero := signedNonzero
    timeInside := materialInside
    material := prepared.referenceWitness.trajectory.movingFamily_material_equation_of_margin prepared.referenceWitness.marginPositive
      globalInside (prepared.referenceWitness.safe time referenceInside) label
    centerIdentity := ?_
    firstPositive := firstPositive
    finalPositive := finalPositive
    weightNonnegative := scalar.1
    massNonnegative := scalar.2.2.2.2.1
    radiusNonnegative := radiusPositive.le
    radiusSmall := radiusSmall
    firstTransverse := firstTransverse.trans eighthLe
    finalTransverse := finalTransverse.trans eighthLe
    firstScale := firstScale
    finalScale := finalScale
    firstSeparated := firstSeparated
    finalSeparated := finalSeparated
    weightBound := weightBound
    massBound := massBound
    forcingSmall := epsilonForcing.trans forcingLe
    epsilonSmall := epsilonSmall
    squaredSmall := squaredSmall
    tailSmall := ?_
    derivativeScale := derivativeSmall
    firstPhysical := firstPhysical
    finalPhysical := finalPhysical
    firstSpectral := firstSpectral
    finalSpectral := finalSpectral
    firstCorrectedArea := firstCorrectedArea
    finalCorrectedArea := finalCorrectedArea
    firstCorrectedTransverse := correctedCap firstTransverse firstCorrectedBound
    finalCorrectedTransverse := correctedCap finalTransverse finalCorrectedBound
    mapSmall := ?_
    quadraticSmall := quadraticSmall
    finalField := finalField }
  · filter_upwards [Ioo_mem_nhds globalInside.1 globalInside.2] with current currentInside
    exact (prepared.referenceWitness.trajectory.movingPatch_centroid_eq_center_of_initial_circles (fun _ => rfl) currentInside label).symm
  · have radiusIdentity : (prepared.referenceWitness.trajectory.movingFamily.patch label).radius = changed.radius (index.val + 1) :=
      prepared.referenceWitness.radiusIdentity index patch
    change (weight / |signedFrequency|) * ((prepared.referenceWitness.trajectory.movingFamily.patch label).radius / firstDistance) ≤ radius ^ 2
    rw [radiusIdentity]
    exact tailSmall
  · simpa only [mapCoefficient, signedFrequency, weight, radius, omega, changed, mul_assoc] using mapSmall

end EulerNonuniqueness.Paper
