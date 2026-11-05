import EulerNonuniqueness.Section6.NormalizedOrbitChartEntry
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics
import EulerNonuniqueness.Section7.ActualIncomingShapeEndpoint
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_straightened_hit_incoming_match
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) :
    ∃ radius > (0 : ℝ), ∀ᶠ incomingTime : ℝ in atBot,
    ∀ accuracy : ℝ, 0 < accuracy →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 ≤ referenceConstant →
    ∃ stableTolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    threshold ≤ 1 / 2 → 0 < factor → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ time ∈ Icc 0 path.stop,
    (∀ current ∈ Icc 0 time, |radialShape prepared.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2) →
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| < radius →
    (referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time).1 =
        coordinate (orbitUnstableShape orbit incomingTime) →
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time).2| < stableTolerance →
    ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
      ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
        index time rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < accuracy := by
  obtain ⟨radius, radiusPositive, constant, constantOne, entry⟩ :=
    normalizedSeparatingOrbit_normalForm_entry_control graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized compatible
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  refine ⟨radius, radiusPositive, ?_⟩
  filter_upwards [entry] with incomingTime entryControl
  intro accuracy accuracyPositive scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant referenceConstant
    rootPositive boundaryNonnegative referenceNonnegative
  obtain ⟨shapeTolerance, shapeTolerancePositive, matching⟩ :=
    scales.eventually_actual_incoming_shape_endpoint amplitudePositive ratioBound alphaPositive orbit normalized incomingTime
      rootPositive boundaryNonnegative accuracyPositive
  let stableTolerance := shapeTolerance / (4 * constant)
  have stableTolerancePositive : 0 < stableTolerance := by dsimp only [stableTolerance]; positivity
  have chartContinuous : ContinuousAt (fun point : ℝ × ℝ =>
      |coordinate point.1| + |point.2 - graph point.1|) 0 :=
    (coordinateSmooth.continuousAt.comp (f := fun point : ℝ × ℝ => point.1) continuousAt_fst).abs.add
      (continuousAt_snd.sub
        (graphSmooth.continuousAt.comp (f := fun point : ℝ × ℝ => point.1) continuousAt_fst)).abs
  have chartSmall : ∀ᶠ point : ℝ × ℝ in 𝓝 0,
      |coordinate point.1| + |point.2 - graph point.1| < stableTolerance :=
    chartContinuous.tendsto.eventually (eventually_lt_nhds (by
      simpa only [Prod.fst_zero, Prod.snd_zero, coordinateZero, graphZero, sub_zero, abs_zero, zero_add] using stableTolerancePositive))
  obtain ⟨referenceRadius, referenceRadiusPositive, referenceInside⟩ := Metric.mem_nhds_iff.mp chartSmall
  refine ⟨stableTolerance, stableTolerancePositive, ?_⟩
  filter_upwards [matching,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative referenceRadiusPositive]
    with frequency matchEstimate referenceSmall
  intro sectionTime phase dipoleAngle threshold shapeRadius factor monitor count prepared path thresholdSmall
    _factorPositive factorSmall index nonterminal time inside radialSmall alternativeSmall unstableHit stableSmall
  let alternative := (unstableShape prepared.trajectory.movingFamily.patchMotion time index,
    stableShape prepared.trajectory.movingFamily.patchMotion time index)
  let reference := (unstableShape prepared.reference time index, stableShape prepared.reference time index)
  have referenceChartSmall : |coordinate reference.1| + |reference.2 - graph reference.1| < stableTolerance := by
    apply referenceInside
    have sharp := referenceSmall prepared time ⟨inside.1, inside.2.trans path.stopBound⟩ index
    have size : |reference.1| + |reference.2| < referenceRadius := by
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < referenceRadius
      linarith only [sharp, abs_nonneg (diagonalDifference prepared.reference time index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1)]
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le (le_add_of_nonneg_right (abs_nonneg reference.2))
      (le_add_of_nonneg_left (abs_nonneg reference.1))).trans_lt size
  have hit : coordinate alternative.1 - coordinate reference.1 = coordinate (orbitUnstableShape orbit incomingTime) := by
    simpa only [referenceStraightenedShape, localNormalFormChart, Prod.fst_sub, alternative, reference] using unstableHit
  have stableBound : |(alternative.2 - graph alternative.1) - (reference.2 - graph reference.1)| < stableTolerance := by
    simpa only [referenceStraightenedShape, localNormalFormChart, Prod.snd_sub, alternative, reference] using stableSmall
  have unstableIdentity : coordinate alternative.1 - coordinate (orbitUnstableShape orbit incomingTime) = coordinate reference.1 := by
    linarith only [hit]
  have stableTriangle := abs_add ((alternative.2 - graph alternative.1) - (reference.2 - graph reference.1))
    (reference.2 - graph reference.1)
  rw [sub_add_cancel] at stableTriangle
  have chartCost : |coordinate alternative.1 - coordinate (orbitUnstableShape orbit incomingTime)| +
      |alternative.2 - graph alternative.1| < stableTolerance + stableTolerance := by
    rw [unstableIdentity]
    linarith only [stableTriangle, stableBound, referenceChartSmall]
  have shapeBound := entryControl alternative alternativeSmall
  have scaled := mul_lt_mul_of_pos_left chartCost constantPositive
  have normalization : constant * (stableTolerance + stableTolerance) = shapeTolerance / 2 := by
    dsimp only [stableTolerance]
    field_simp [constantPositive.ne']
    ring
  rw [normalization] at scaled
  have shapeClose : |unstableShape prepared.trajectory.movingFamily.patchMotion time index - orbitUnstableShape orbit incomingTime| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index - orbitStableShape orbit incomingTime| < shapeTolerance := by
    exact (shapeBound.trans_lt scaled).trans (half_lt_self shapeTolerancePositive)
  exact matchEstimate prepared path thresholdSmall factorSmall index nonterminal time inside.1 inside.2 radialSmall shapeClose

end EulerNonuniqueness.Paper
