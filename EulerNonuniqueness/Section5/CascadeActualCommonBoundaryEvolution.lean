import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryRecord
import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryEvolution
import EulerNonuniqueness.Section3.MovingCanonicalCommonPairEquation

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6 FiniteMovingPatchFamily

local instance actualCommonBoundaryEvolutionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem exists_uniform_actual_common_boundary_evolution (caps : CanonicalCommonBoundaryRateCaps) :
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
      ∀ time ∈ Ioo 0 path.stop, ∀ (index : Fin count) (patch : Fin 4),
      let changed : Scales := {scales with frequency := frequency}
      let label := finProdFinEquiv (index, patch)
      let omega := changed.omega (index.val + 1)
      ∃ comparison : CanonicalCommonBoundaryPairAt caps prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
        label label (patchSign patch * changed.amplitude * omega ^ 4) time
        (changed.length (index.val + 1) / 400) (factor * changed.length (index.val + 1) / 400)
        (changed.referenceLocalExteriorWeight (index.val + 1)) (2 * changed.circulation (index.val + 1))
        (radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2))
        (prepared.referenceWitness.trajectory.spectralCoordinate label time)
        (prepared.trajectory.spectralCoordinate label time),
      CanonicalCommonBoundaryEvolutionAt comparison
        (prepared.referenceWitness.trajectory.spectralCoordinate label)
        (prepared.trajectory.spectralCoordinate label) := by
  obtain ⟨equationRadius, equationPositive, equations⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_actual_common_pair_equation_radius
  obtain ⟨recordCap, recordPositive, records⟩ := exists_uniform_actual_common_boundary_record caps
  obtain ⟨shapeCap, shapePositive, shapes⟩ := exists_actual_source_stopped_shape_radius_monotone caps.rawPositive
  let rawCap := min equationRadius (min recordCap shapeCap)
  refine ⟨rawCap, lt_min equationPositive (lt_min recordPositive shapePositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨coefficient, coefficientOne, recordRoot, recordEight, recordBounds⟩ := records factor factorPositive factorSmall
  obtain ⟨materialRoot, materialEight, materialBounds⟩ :=
    exists_uniform_actual_common_boundary_material_envelopes factor factorPositive factorSmall
  let rootMin := max recordRoot materialRoot
  refine ⟨coefficient, coefficientOne, rootMin, recordEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [recordBounds scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    materialBounds scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative] with frequency record material
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path time inside index patch
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let label := finProdFinEquiv (index, patch)
  let signedFrequency := patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4
  let firstDistance := changed.length (index.val + 1) / 400
  let finalDistance := factor * changed.length (index.val + 1) / 400
  let weight := changed.referenceLocalExteriorWeight (index.val + 1)
  let mass := 2 * changed.circulation (index.val + 1)
  have closedInside : time ∈ Icc 0 path.stop := ⟨inside.1.le, inside.2.le⟩
  have comparison := record count orbit sectionTime phase dipoleAngle prepared requestedPositive
    (requestedSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) path time closedInside index patch
  have geometry := material count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time closedInside index patch
  obtain ⟨firstScale, finalScale, firstNear, finalNear⟩ := geometry
  have firstPositive : 0 < firstDistance := comparison.firstPositive
  have finalPositive : 0 < finalDistance := comparison.finalPositive
  have firstDensity : prepared.referenceWitness.configuration.density label = signedFrequency :=
    prepared.referenceWitness.densityIdentity index patch
  have finalDensity : prepared.configuration.density label = signedFrequency := prepared.densityIdentity index patch
  have firstNonzero : prepared.referenceWitness.configuration.density label ≠ 0 := by
    rw [firstDensity]
    exact comparison.frequencyNonzero
  have densityIdentity : prepared.configuration.density label = prepared.referenceWitness.configuration.density label :=
    finalDensity.trans firstDensity.symm
  have firstSafe : ∀ current ∈ Icc 0 path.stop, prepared.referenceWitness.margin ≤
      infDist (prepared.referenceWitness.trajectory.curve current)
        (prepared.referenceWitness.configuration.movingStateAdmissible 4 prepared.referenceWitness.shapeRadius prepared.referenceWitness.gap)ᶜ := by
    intro current member
    exact prepared.referenceWitness.safe current ⟨member.1, by linarith [member.2, path.stopBound]⟩
  have rawSmall := prepared.raw_shape_caps requestedPositive path closedInside label
  have physicalCap : requestedCap ≤ equationRadius := requestedSmall.trans (min_le_left _ _)
  have firstActual := equations prepared.referenceWitness.trajectory prepared.referenceWitness.trajectory label label
    (horizon := path.stop) (time := time) (firstDistance := firstDistance) (finalDistance := firstDistance)
    (weight := weight) (mass := mass) (fun _ => rfl) (fun _ => rfl) rfl
    prepared.referenceWitness.marginPositive prepared.referenceWitness.marginPositive
    (by linarith [path.stopBound]) (by linarith [path.stopBound]) firstSafe firstSafe firstNonzero rfl inside
    firstPositive firstPositive comparison.weightNonnegative comparison.massNonnegative firstScale firstScale firstNear
    comparison.firstSeparated (rawSmall.1.trans_le physicalCap)
  have finalActual := equations prepared.referenceWitness.trajectory prepared.trajectory label label
    (horizon := path.stop) (time := time) (firstDistance := firstDistance) (finalDistance := finalDistance)
    (weight := weight) (mass := mass) (fun _ => rfl) (fun _ => rfl) rfl
    prepared.referenceWitness.marginPositive prepared.marginPositive
    (by linarith [path.stopBound]) (by linarith [path.stopBound]) firstSafe
    (fun current member => (path.safe current member).le) firstNonzero densityIdentity inside
    firstPositive finalPositive comparison.weightNonnegative comparison.massNonnegative firstScale finalScale firstNear
    comparison.finalSeparated (rawSmall.2.trans_le physicalCap)
  obtain ⟨firstSeparated, firstSmall, firstEquation⟩ := firstActual
  obtain ⟨finalSeparated, finalSmall, finalEquation⟩ := finalActual
  rw [firstDensity] at firstEquation finalEquation
  have reconstruction (current : ℝ) (member : current ∈ Icc 0 path.stop) :
      diskPhysicalSpectralChart (prepared.referenceWitness.trajectory.spectralCoordinate label current) =
          (prepared.referenceWitness.trajectory.curve current).2.2 label ∧
      diskPhysicalSpectralChart (prepared.trajectory.spectralCoordinate label current) =
          (prepared.trajectory.curve current).2.2 label := by
    obtain ⟨firstShape, finalShape⟩ := shapes prepared
      (requestedSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) path current member label
    exact ⟨firstShape.reconstruct, finalShape.reconstruct⟩
  have atTime := reconstruction time closedInside
  have firstCurveEquality : (fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonPhysicalCoordinate label
      signedFrequency current (diskPhysicalSpectralChart (prepared.referenceWitness.trajectory.spectralCoordinate label current))) =ᶠ[𝓝 time]
      (fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonPhysicalCoordinate label
        signedFrequency current ((prepared.referenceWitness.trajectory.curve current).2.2 label)) := by
    filter_upwards [Ioo_mem_nhds inside.1 inside.2] with current member
    rw [(reconstruction current ⟨member.1.le, member.2.le⟩).1]
  have finalCurveEquality : (fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonPhysicalCoordinate label
      signedFrequency current (diskPhysicalSpectralChart (prepared.trajectory.spectralCoordinate label current))) =ᶠ[𝓝 time]
      (fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonPhysicalCoordinate label
        signedFrequency current ((prepared.trajectory.curve current).2.2 label)) := by
    filter_upwards [Ioo_mem_nhds inside.1 inside.2] with current member
    rw [(reconstruction current ⟨member.1.le, member.2.le⟩).2]
  refine ⟨comparison, ?_⟩
  with_reducible_and_instances refine ⟨rfl, rfl, ?_, ?_⟩
  · have actual := firstEquation.congr_of_eventuallyEq firstCurveEquality
    with_reducible_and_instances
      simpa only [← atTime.1, CanonicalCommonBoundaryPairAt.firstResidual, sub_self, map_zero, add_zero] using actual
  · have actual := finalEquation.congr_of_eventuallyEq finalCurveEquality
    with_reducible_and_instances
      simpa only [← atTime.2, CanonicalCommonBoundaryPairAt.finalResidual, CanonicalCommonBoundaryPairAt.sourceDifference] using actual

end EulerNonuniqueness.Paper
