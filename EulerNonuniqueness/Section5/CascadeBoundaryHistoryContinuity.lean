import EulerNonuniqueness.Section5.CascadeCommonBoundaryMaterialEnvelopes
import EulerNonuniqueness.Section5.CascadeSourceShapeRadius
import EulerNonuniqueness.Section3.CanonicalExteriorCoefficientPairContinuity
import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseBounds

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance boundaryHistoryContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

open EulerNonuniqueness.Section6 FiniteMovingPatchFamily

theorem exists_uniform_actual_canonical_boundary_coefficient_continuity
    (factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot →
    scales.amplitude = scaleRoot ^ 3 → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ (index : Fin count) (patch : Fin 4),
      ContinuousOn (canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily
        prepared.trajectory.movingFamily (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch)))
        (Icc 0 path.stop) := by
  obtain ⟨rootMin, rootEight, parameters⟩ :=
    exists_uniform_actual_common_boundary_material_envelopes factor factorPositive factorSmall
  refine ⟨rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [parameters scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    threshold referenceConstant thresholdSmall referenceNonnegative] with frequency material
  intro count orbit sectionTime phase dipoleAngle shapeRadius monitor boundaryConstant prepared path index patch time inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  let label := finProdFinEquiv (index, patch)
  let firstDistance := changed.length (index.val + 1) / 400
  let finalDistance := factor * changed.length (index.val + 1) / 400
  obtain ⟨firstScale, finalScale, firstNear, finalNear⟩ :=
    material count orbit sectionTime phase dipoleAngle prepared path time inside index patch
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have firstInside (source : Fin (count * 4)) (_ : source ∈ Finset.univ.erase label) :
      time ∈ Ioo (first.patch source).initialTime (first.patch source).finalTime := by
    exact globalInside
  have finalInside (source : Fin (count * 4)) (_ : source ∈ Finset.univ.erase label) :
      time ∈ Ioo (final.patch source).initialTime (final.patch source).finalTime := by
    exact globalInside
  have firstWeightNonnegative : 0 ≤ changed.referenceLocalExteriorWeight (index.val + 1) :=
    (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans firstNear.self_of_nhds.2.1
  have finalWeightNonnegative : 0 ≤ changed.cascadeLocalExteriorWeight factor (index.val + 1) :=
    (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans finalNear.self_of_nhds.2.1
  exact (first.canonicalExteriorCoefficientPairSeries_continuousAt_geometric final label label
    (time := time) (firstDistance := firstDistance) (finalDistance := finalDistance)
    (firstWeight := changed.referenceLocalExteriorWeight (index.val + 1))
    (finalWeight := changed.cascadeLocalExteriorWeight factor (index.val + 1))
    (div_pos (changed.length_pos _) (by norm_num))
    (div_pos (mul_pos factorPositive (changed.length_pos _)) (by norm_num))
    firstWeightNonnegative finalWeightNonnegative firstScale finalScale firstInside finalInside
    firstNear.self_of_nhds.1 finalNear.self_of_nhds.1
    (firstNear.mono fun _ actual => actual.2.1)
    (finalNear.mono fun _ actual => actual.2.1)).continuousWithinAt

theorem exists_uniform_actual_raw_spectral_continuity :
    ∃ rawCap > (0 : ℝ),
    ∀ {requestedCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
      {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair requestedCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    0 < requestedCap → requestedCap ≤ rawCap →
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ label : Fin (count * 4),
    ContinuousOn (prepared.referenceWitness.trajectory.spectralCoordinate label) (Icc 0 path.stop) ∧
      ContinuousOn (prepared.trajectory.spectralCoordinate label) (Icc 0 path.stop) := by
  obtain ⟨rawCap, rawPositive, _, _, derivatives, _⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds
  refine ⟨rawCap, rawPositive, ?_⟩
  intro requestedCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius
    factor monitor boundaryConstant count prepared requestedPositive requestedSmall path label
  have firstContinuous : Continuous (fun current => (prepared.referenceWitness.trajectory.curve current).2.2 label) :=
    (continuous_apply label).comp (continuous_snd.comp (continuous_snd.comp prepared.referenceWitness.trajectory.continuous))
  have finalContinuous : Continuous (fun current => (prepared.trajectory.curve current).2.2 label) :=
    (continuous_apply label).comp (continuous_snd.comp (continuous_snd.comp prepared.trajectory.continuous))
  constructor <;> intro time inside
  · have cap := (prepared.raw_shape_caps requestedPositive path inside label).1.le.trans requestedSmall
    have actual := ContinuousAt.comp (g := diskPhysicalSpectralCoordinate)
      (f := fun current => (prepared.referenceWitness.trajectory.curve current).2.2 label)
      (derivatives _ cap).1.continuousAt (firstContinuous.continuousAt (x := time))
    simpa only [MovingCentroidGaugeTrajectory.spectralCoordinate, Function.comp_def] using
      (actual.continuousWithinAt (s := Icc 0 path.stop))
  · have cap := (prepared.raw_shape_caps requestedPositive path inside label).2.le.trans requestedSmall
    have actual := ContinuousAt.comp (g := diskPhysicalSpectralCoordinate)
      (f := fun current => (prepared.trajectory.curve current).2.2 label)
      (derivatives _ cap).1.continuousAt (finalContinuous.continuousAt (x := time))
    simpa only [MovingCentroidGaugeTrajectory.spectralCoordinate, Function.comp_def] using
      (actual.continuousWithinAt (s := Icc 0 path.stop))

end EulerNonuniqueness.Paper
