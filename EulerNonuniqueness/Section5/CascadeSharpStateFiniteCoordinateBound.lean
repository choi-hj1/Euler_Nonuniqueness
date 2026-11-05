import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_uniform_actual_sharp_state_finite_coordinate_bound
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {cap : ℝ} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    ContinuousOn (prepared.finiteCoordinateSize graph coordinate suppliedLift index) (Icc 0 finish) ∧
    prepared.finiteCoordinateSize graph coordinate suppliedLift index 0 = 0 ∧
    ∀ time ∈ Icc 0 finish,
      prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖ +
        ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
          quadrupoleCenter prepared.reference time index‖ /
            ({scales with frequency := frequency} : Scales).location (index.val + 1) +
        (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤
      constant * (prepared.finiteCoordinateSize graph coordinate suppliedLift index time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) := by
  obtain ⟨radius, radiusPositive, radiusQuarter, geometryConstant, geometryOne, geometry⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, radiusQuarter, geometryConstant + 1, by linarith only [geometryOne], ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [geometry scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorSmall thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative]
    with frequency geometryEstimate coherence
  intro cap orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small suppliedLift suppliedContinuous suppliedInitial suppliedPolar
  obtain ⟨lift, liftContinuous, liftPolar, coordinateContinuous, coordinateInitial, _, estimates⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound small
  have equality := coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans radiusQuarter) lift suppliedLift
    (fun side => (liftContinuous side).1.continuousOn) suppliedContinuous
    (fun side => (liftContinuous side).2.trans (suppliedInitial side).symm) liftPolar suppliedPolar
  have coordinateEquality := equality.2.2 graph coordinate
  refine ⟨coordinateContinuous.congr (fun time inside => (coordinateEquality inside).symm), ?_, ?_⟩
  · rw [← coordinateEquality (show (0 : ℝ) ∈ Icc 0 finish from ⟨le_rfl, finishNonnegative⟩)]
    exact coordinateInitial
  · intro time inside
    let changed : Scales := {scales with frequency := frequency}
    let coordinateSize := prepared.finiteCoordinateSize graph coordinate suppliedLift index time
    let moment := ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖
    let center := ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
      quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1)
    let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
    have centeredBound := (estimates time inside).1
    rw [coordinateEquality inside] at centeredBound
    have components : moment + center ≤ coordinateSize := by
      let extra := |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2| +
        |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index - diagonalDifference prepared.reference time index| /
          changed.length (index.val + 1) ^ 2 +
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift
          (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|
      have extraNonnegative : 0 ≤ extra := by dsimp only [extra]; positivity
      have bound := le_add_of_nonneg_left (a := moment + center) extraNonnegative
      convert bound using 1
      dsimp only [coordinateSize, CascadeSourcePreparedPair.finiteCoordinateSize, extra, moment, center, changed]
      ring
    have rawNonnegative : 0 ≤ raw := by
      dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have scaledRaw := mul_nonneg (zero_le_one.trans geometryOne) rawNonnegative
    change prepared.rawSourceCenteredState time index + moment + center + raw ≤
      (geometryConstant + 1) * (coordinateSize + raw)
    calc
      _ ≤ geometryConstant * coordinateSize + coordinateSize + raw := by linarith only [centeredBound, components]
      _ ≤ (geometryConstant + 1) * (coordinateSize + raw) := by nlinarith only [scaledRaw]

end EulerNonuniqueness.Paper
