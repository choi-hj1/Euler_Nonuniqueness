import EulerNonuniqueness.Section5.CascadeStoppedShapeContinuity
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateGeometry
import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.General.ContinuousPrefixBootstrap

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_full_state_physical_refinement
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    {requestedRadius : ℝ} (requestedPositive : 0 < requestedRadius) :
    ∃ precision > (0 : ℝ),
    ∀ scales : Scales, 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ {cap : ℝ} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, 0 < factor →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish ∈ Icc 0 path.stop,
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ time ∈ Icc 0 finish,
      prepared.finiteCoordinateSize graph coordinate suppliedLift index time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤ precision) →
    ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| < requestedRadius := by
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverse⟩ :=
    Section6.localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  let radius := min requestedRadius (inverseRadius / 2)
  have radiusPositive : 0 < radius := lt_min requestedPositive (half_pos inversePositive)
  have radiusRequested : radius ≤ requestedRadius := min_le_left _ _
  have radiusInverse : radius < inverseRadius := by
    have bound : radius ≤ inverseRadius / 2 := min_le_right _ _
    linarith only [bound, inversePositive]
  have constantPositive : 0 < inverseConstant := zero_lt_one.trans_le inverseOne
  let precision := radius / (32 * inverseConstant)
  have precisionPositive : 0 < precision := by dsimp only [precision]; positivity
  have coefficient : inverseConstant * precision ≤ radius / 8 := by
    have identity : inverseConstant * precision = radius / 32 := by dsimp only [precision]; field_simp; ring
    rw [identity]
    linarith only [radiusPositive]
  refine ⟨precision, precisionPositive, ?_⟩
  intro scales ratioBound alphaPositive referenceConstant referenceNonnegative
  filter_upwards [scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
    (by positivity : 0 < radius / 8)] with frequency referenceSmall
  intro cap orbit sectionTime phase dipoleAngle threshold scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path factorPositive index nonterminal finish finishInside small suppliedLift fullBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let size := fun time => |unstableShape motion time index| + |stableShape motion time index|
  have regular := path.shape_continuousOn_of_small factorPositive index finishInside small
  have sizeContinuous : ContinuousOn size (Icc 0 finish) := regular.1.abs.add regular.2.abs
  have referenceBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < radius / 8 := by
    have bound := referenceSmall prepared.toCascadeMaterialPreparedPair time
      ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ index
    linarith only [bound, abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  have initialSmall : size 0 < radius := by
    have positiveInitial : positiveHalfDiagonal motion 0 index = positiveHalfDiagonal prepared.reference 0 index := by
      simp only [motion, positiveHalfDiagonal, prepared.toCascadeMaterialPreparedPair.nonterminal_initial_centroid index nonterminal]
    have negativeInitial : negativeHalfDiagonal motion 0 index = negativeHalfDiagonal prepared.reference 0 index := by
      simp only [motion, negativeHalfDiagonal, prepared.toCascadeMaterialPreparedPair.nonterminal_initial_centroid index nonterminal]
    have initial : size 0 = |unstableShape prepared.reference 0 index| + |stableShape prepared.reference 0 index| := by
      dsimp only [size, unstableShape, stableShape, radialShape, angularShape]
      rw [positiveInitial, negativeInitial]
    rw [initial]
    have bound := referenceBound 0 ⟨le_rfl, finishInside.1⟩
    linarith only [bound, radiusPositive]
  have improve (time : ℝ) (inside : time ∈ Icc 0 finish) (weak : size time ≤ radius) : size time < radius / 2 := by
    let first := (unstableShape motion time index, stableShape motion time index)
    let second := (unstableShape prepared.reference time index, stableShape prepared.reference time index)
    have secondSmall : |second.1| + |second.2| < inverseRadius := by
      have bound := referenceBound time inside
      change |second.1| + |second.2| < radius / 8 at bound
      linarith only [bound, radiusInverse, radiusPositive]
    have distance := inverse first second (weak.trans_lt radiusInverse) secondSmall
    have normBound : ‖Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second‖ ≤
        |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).1| +
        |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    have chartBound : |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).1| +
        |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).2| ≤ precision := by
      have actual := fullBound time inside
      have locationPositive := changed.location_pos (index.val + 1)
      have lengthPositive := changed.length_pos (index.val + 1)
      have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
        apply Finset.sum_nonneg
        intro patch _
        dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
        positivity
      have extra : 0 ≤ |diagonalDifference motion time index - diagonalDifference prepared.reference time index| / changed.length (index.val + 1) ^ 2 +
          |relativeCorrectedPaperPhase (Section6.phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| +
          ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
          ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) +
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by positivity
      dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize] at actual
      change |(referenceStraightenedShape motion graph coordinate index time).1 - (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 - (referenceStraightenedShape prepared.reference graph coordinate index time).2| ≤ precision
      linarith only [actual, extra]
    have physical := distance.trans (mul_le_mul_of_nonneg_left (normBound.trans chartBound) constantPositive.le)
    have firstTriangle := abs_sub_abs_le_abs_sub first.1 second.1
    have secondTriangle := abs_sub_abs_le_abs_sub first.2 second.2
    have reference := referenceBound time inside
    dsimp only [first, second] at physical firstTriangle secondTriangle
    change size time < radius / 2
    nlinarith only [physical, firstTriangle, secondTriangle, reference, coefficient, radiusPositive]
  have confined := strictly_negative_of_prefix_improvement (sizeContinuous.sub continuousOn_const) (sub_neg.mpr initialSmall) (by
    intro time inside weak
    exact sub_neg.mpr ((improve time inside (sub_nonpos.mp (weak time ⟨inside.1, le_rfl⟩))).trans (half_lt_self radiusPositive)))
  intro time inside
  exact (improve time inside (sub_neg.mp (confined time inside)).le).trans_le
    ((by linarith only [radiusPositive] : radius / 2 ≤ radius).trans radiusRequested)

end EulerNonuniqueness.Paper
