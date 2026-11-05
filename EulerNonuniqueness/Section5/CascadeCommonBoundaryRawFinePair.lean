import EulerNonuniqueness.Section4.ReferenceNonstrictFineConfinement
import EulerNonuniqueness.Section5.CascadeCommonBoundaryFineMonitor
import EulerNonuniqueness.Section5.CascadeSourceShapeRadius
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_common_boundary_raw_fine_pair :
    ∃ rawCap > 0, ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ coefficient ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
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
      ‖diskPhysicalTransverseProjection
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)‖ <
          (coefficient / (scaleRoot ^ 2 * ({scales with frequency := frequency}).omega (index.val + 1) ^ 2)) / 8 ∧
      ‖diskPhysicalTransverseProjection
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)‖ <
          (coefficient / (scaleRoot ^ 2 * ({scales with frequency := frequency}).omega (index.val + 1) ^ 2)) / 8 := by
  obtain ⟨referenceMonitor, referenceMonitorPositive, referenceConstant, referenceOne, referenceConfinement⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_reference_nonstrict_contour_confinement_on_horizon
  obtain ⟨alternativeMonitor, alternativeMonitorPositive, alternativeConfinement⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_common_boundary_comoving_fine_monitor
  let rawCap := min referenceMonitor alternativeMonitor
  have rawPositive : 0 < rawCap := lt_min referenceMonitorPositive alternativeMonitorPositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨alternativeConstant, alternativeOne, alternativeHorizons⟩ :=
    alternativeConfinement factor factorPositive factorSmall
  obtain ⟨referenceRoot, referenceEight, referenceFine⟩ := referenceConfinement 2 (by norm_num)
  obtain ⟨alternativeRoot, alternativeEight, alternativeFine⟩ := alternativeHorizons 1 zero_le_one
  let coefficient := max (referenceConstant + 1) (alternativeConstant + 1)
  let rootMin := max referenceRoot alternativeRoot
  have coefficientOne : 1 ≤ coefficient := by
    dsimp only [coefficient]
    exact (show 1 ≤ referenceConstant + 1 by linarith).trans (le_max_left _ _)
  refine ⟨coefficient, coefficientOne, rootMin, referenceEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold actualReferenceConstant thresholdSmall referenceNonnegative
  have rootEight : 8 ≤ scaleRoot := referenceEight.trans ((le_max_left _ _).trans rootLarge)
  have rootPositive : 0 < scaleRoot := by linarith
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [scales.eventually_universal_reference_mechanical_data amplitudePositive ratioLarge alphaPositive
      thresholdSmall referenceNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioLarge alphaPositive factorPositive factorSmall
      (bound := 3) (le_refl _),
    eventually_ge_atTop (1 : ℝ),
    (scales.strain_tendsto_zero ratioLarge alphaPositive).eventually (eventually_lt_nhds zero_lt_one)]
    with frequency mechanical geometry frequencyOne strainSmall
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path
  let changed : Scales := {scales with frequency := frequency}
  have referenceShape (current : ℝ) (inside : current ∈ Icc (0 : ℝ) 2) (label : Fin (count * 4)) :
      ‖(prepared.referenceWitness.trajectory.curve current).2.2 label - standardCircleBanach‖ < referenceMonitor :=
    (prepared.referenceShapeCap current inside label).trans_le (requestedSmall.trans (min_le_left _ _))
  have alternativeShape (current : ℝ) (inside : current ∈ Icc 0 path.stop) (label : Fin (count * 4)) :
      ‖(prepared.trajectory.curve current).2.2 label - standardCircleBanach‖ < alternativeMonitor :=
    ((prepared.raw_shape_caps requestedPositive path inside label).2).trans_le (requestedSmall.trans (min_le_right _ _))
  have referenceActual := referenceFine changed scaleRoot ((le_max_left _ _).trans rootLarge)
    2 (by norm_num) (le_refl _) amplitudeIdentity frequencyOne ratioLarge alphaPositive strainSmall.le
    prepared.referenceWitness.trajectory prepared.referenceWitness.densityIdentity prepared.referenceWitness.radiusIdentity
    (fun _ => rfl) rfl prepared.referenceWitness.marginPositive (by norm_num) prepared.referenceWitness.safe
    (fun current inside index => (mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
      prepared.referenceWitness.evolution prepared.referenceWitness.coarse current inside index).1)
    referenceShape prepared.referenceWitness.continuousVectors
  have alternativeActual := alternativeFine changed scaleRoot ((le_max_right _ _).trans rootLarge)
    path.stop path.stopPositive.le path.stopBound amplitudeIdentity frequencyOne ratioLarge alphaPositive strainSmall.le
    prepared.trajectory prepared.densityIdentity prepared.radiusIdentity (fun _ => rfl) rfl prepared.marginPositive
    (by linarith [path.stopBound]) (fun current inside => (path.safe current inside).le)
    (fun current inside => path.safe current ⟨inside.1, inside.2.le⟩)
    (fun current inside => path.internalClosed current inside)
    (fun current inside label => (path.externalMonitors current inside (.extent label)).le)
    (fun current inside receiver source => (path.externalMonitors current inside (.lower receiver source)).le)
    (fun index => (geometry (index.val + 1)).2.2.1)
    (fun index => (geometry (index.val + 1)).2.1)
    (fun index => (geometry (index.val + 1)).2.2.2)
    alternativeShape
    (fun current inside label => prepared.continuousVectors current
      ⟨inside.1, by linarith [inside.2, path.stopBound]⟩ label)
  intro time inside index patch
  have denominatorNonnegative : 0 ≤ scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2 := by positivity
  have referenceLe := div_le_div_of_nonneg_right (le_max_left (referenceConstant + 1) (alternativeConstant + 1)) denominatorNonnegative
  have alternativeLe := div_le_div_of_nonneg_right (le_max_right (referenceConstant + 1) (alternativeConstant + 1)) denominatorNonnegative
  refine ⟨(referenceActual time ⟨inside.1, by linarith [inside.2, path.stopBound]⟩ index patch).trans_le
    (div_le_div_of_nonneg_right referenceLe (by norm_num)),
    (alternativeActual time inside index patch).trans_le (div_le_div_of_nonneg_right alternativeLe (by norm_num))⟩

end EulerNonuniqueness.Paper
