import EulerNonuniqueness.Section6.NormalizedOrbitChartEntry
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics
import EulerNonuniqueness.Section5.CascadeNormalizedPointEquation
import EulerNonuniqueness.Section5.CascadePrehitMatchingAccuracy
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section5.CascadePairedSaddleAdmissibility
import EulerNonuniqueness.Section6.HalfDiagonalCanonicalConfigurationMatching
import EulerNonuniqueness.Section6.HalfDiagonalMatchingPhase

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_stable_tolerance_actual_straightened_hit_incoming_match
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) :
    ∃ radius > (0 : ℝ), ∀ᶠ incomingTime : ℝ in atBot,
    ∀ accuracy : ℝ, 0 < accuracy → ∃ stableTolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
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
    ∀ lift : Fin 2 → ℝ → ℝ,
    (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ current ∈ Icc 0 time,
      positiveHalfDiagonal (cascadePairedMotion prepared side) current index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared side) current index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side current : ℂ))) →
    let rotation := Complex.exp (Complex.I * ((lift 0 time - orbit.phase incomingTime : ℝ) : ℂ))
    halfDiagonalMatchingRotation (positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index)
      (orbit.positive incomingTime) = rotation ∧ ‖rotation‖ = 1 ∧
      ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
        index time rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < accuracy := by
  obtain ⟨radius, radiusPositive, constant, constantOne, entry⟩ :=
    normalizedSeparatingOrbit_normalForm_entry_control graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized compatible
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  refine ⟨radius, radiusPositive, ?_⟩
  filter_upwards [entry] with incomingTime entryControl
  intro accuracy accuracyPositive
  have referenceDifference : 0 < ‖orbit.positive incomingTime‖ ^ 2 - ‖orbit.negative incomingTime‖ ^ 2 := by
    rw [(normalized.2.1 incomingTime).1]
    norm_num
  obtain ⟨shapeTolerance, shapeTolerancePositive, matching⟩ :=
    exists_halfDiagonal_canonical_configuration_matching (orbit.positive incomingTime)
      (orbit.negative incomingTime) referenceDifference accuracyPositive
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
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant referenceConstant
    rootPositive boundaryNonnegative referenceNonnegative
  filter_upwards [scales.eventually_material_prehit_matching_accuracy amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative (lt_min shapeTolerancePositive (by norm_num : (0 : ℝ) < 1 / 2)),
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative referenceRadiusPositive]
    with frequency quantitative referenceSmall
  intro sectionTime phase dipoleAngle threshold shapeRadius factor monitor count prepared path thresholdSmall
    _factorPositive factorSmall index nonterminal time inside radialSmall alternativeSmall unstableHit stableSmall
    lift _liftProperties polar
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
  let motion := prepared.trajectory.movingFamily.patchMotion
  let changed : Scales := {scales with frequency := frequency}
  let positive := positiveHalfDiagonal motion time index
  let negative := negativeHalfDiagonal motion time index
  let canonical := halfDiagonalMatchingRotation positive (orbit.positive incomingTime)
  have data := quantitative prepared path thresholdSmall factorSmall index nonterminal time inside.1 inside.2
    radialSmall time ⟨inside.1, le_rfl⟩
  have diagonalClose := data.1.trans_le (min_le_left shapeTolerance (1 / 2))
  have neutralClose := data.2.trans_le (min_le_left shapeTolerance (1 / 2))
  have halfBound := data.1.trans_le (min_le_right shapeTolerance (1 / 2))
  have differencePositive : 0 < diagonalDifference motion time index := by
    have lower := (abs_lt.mp halfBound).1
    have ratioPositive : 0 < diagonalDifference motion time index / changed.length (index.val + 1) ^ 2 := by
      linarith only [lower]
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos (changed.length_pos _))).mp ratioPositive
  have positiveNonzero : positive ≠ 0 := by
    have normPositive : 0 < ‖positive‖ := by
      change 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2 at differencePositive
      nlinarith only [differencePositive, sq_nonneg ‖negative‖, norm_nonneg positive]
    exact norm_pos_iff.mp normPositive
  have shapeBound : ‖halfDiagonalShape positive negative -
      halfDiagonalShape (orbit.positive incomingTime) (orbit.negative incomingTime)‖ < shapeTolerance := by
    change ‖(unstableShape motion time index - orbitUnstableShape orbit incomingTime,
      stableShape motion time index - orbitStableShape orbit incomingTime)‖ < shapeTolerance
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    constructor <;> linarith only [shapeClose,
      abs_nonneg (unstableShape motion time index - orbitUnstableShape orbit incomingTime),
      abs_nonneg (stableShape motion time index - orbitStableShape orbit incomingTime)]
  have normalizedDifference : |(‖positive‖ ^ 2 - ‖negative‖ ^ 2) / changed.length (index.val + 1) ^ 2 -
      (‖orbit.positive incomingTime‖ ^ 2 - ‖orbit.negative incomingTime‖ ^ 2)| < shapeTolerance := by
    simpa only [(normalized.2.1 incomingTime).1] using diagonalClose
  have canonicalData := matching positive negative (centroidAsymmetry motion time index)
    (changed.length (index.val + 1)) (changed.length_pos _) differencePositive normalizedDifference shapeBound neutralClose
  have identity : cascadeNormalizedPointPositions changed motion index time canonical 0 =
      fun patch => ((changed.length (index.val + 1) : ℂ) * canonical)⁻¹ *
        quadrupoleCentroidOffset positive negative (centroidAsymmetry motion time index) patch := by
    funext patch
    simp only [cascadeNormalizedPointPositions, zero_div, add_zero, fourPointCenterProjection]
    change _ * (patchCentroid motion time index patch - quadrupoleCenter motion time index) = _
    rw [patchCentroid_sub_quadrupoleCenter]
    rfl
  have phaseIdentity := normalizedSeparatingOrbit_matchingRotation_eq_phase_difference orbit normalized incomingTime
    positiveNonzero (polar 0 time ⟨inside.1, le_rfl⟩)
  dsimp only
  refine ⟨phaseIdentity, ?_, ?_⟩
  · rw [← phaseIdentity]
    exact canonicalData.1
  · rw [← phaseIdentity, identity]
    exact canonicalData.2

end EulerNonuniqueness.Paper
