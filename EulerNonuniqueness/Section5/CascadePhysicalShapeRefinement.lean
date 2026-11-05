import EulerNonuniqueness.Section5.CascadeStoppedShapeContinuity
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.General.ContinuousPrefixBootstrap
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics
import EulerNonuniqueness.Section5.Delay
import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- An actual small-branch profile confines the physical shape in any prescribed smaller neighborhood. -/
theorem exists_uniform_actual_physical_shape_refinement
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    {requestedRadius : ℝ} (requestedPositive : 0 < requestedRadius)
    {magnitude : ℝ} (magnitudeNonnegative : 0 ≤ magnitude) :
    ∃ endpoint > (0 : ℝ), endpoint ≤ 1 ∧
    ∀ scales : Scales, 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, 0 < factor →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish ∈ Icc 0 path.stop,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let shape := fun time =>
      |(referenceStraightenedShape motion graph coordinate index time -
        referenceStraightenedShape prepared.reference graph coordinate index time).1| +
      |(referenceStraightenedShape motion graph coordinate index time -
        referenceStraightenedShape prepared.reference graph coordinate index time).2|
    (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) →
    ∀ origin : ℝ,
    (∀ time ∈ Icc 0 finish, shape time ≤ magnitude * changed.seed (index.val + 1) *
      Real.exp (growth * (time - origin))) →
    changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpoint →
    ∀ time ∈ Icc 0 finish,
      |unstableShape motion time index| + |stableShape motion time index| < requestedRadius := by
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverse⟩ :=
    Section6.localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  have inversePositive' : 0 < inverseConstant := zero_lt_one.trans_le inverseOne
  let radius := min requestedRadius (inverseRadius / 2)
  have radiusPositive : 0 < radius := lt_min requestedPositive (half_pos inversePositive)
  have radiusRequested : radius ≤ requestedRadius := min_le_left _ _
  have radiusInverse : radius < inverseRadius := by
    have bound : radius ≤ inverseRadius / 2 := min_le_right _ _
    linarith only [bound, inversePositive]
  let endpoint := min 1 (radius / (8 * inverseConstant * (1 + magnitude)))
  have endpointPositive : 0 < endpoint := by dsimp only [endpoint]; positivity
  have endpointBudget : inverseConstant * magnitude * endpoint ≤ radius / 8 := by
    have scaled := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (radius / (8 * inverseConstant * (1 + magnitude))))
      (by positivity : 0 ≤ 8 * inverseConstant * (1 + magnitude))
    have identity : (8 * inverseConstant * (1 + magnitude)) *
        (radius / (8 * inverseConstant * (1 + magnitude))) = radius := by field_simp
    rw [identity] at scaled
    have slack : 0 ≤ inverseConstant * endpoint := mul_nonneg inversePositive'.le endpointPositive.le
    change 8 * inverseConstant * (1 + magnitude) * endpoint ≤ radius at scaled
    linear_combination (1 / 8 : ℝ) * scaled + slack
  refine ⟨endpoint, endpointPositive, min_le_left _ _, ?_⟩
  intro scales ratioBound alphaPositive referenceConstant referenceNonnegative
  filter_upwards [scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
    (by positivity : 0 < radius / 8), eventually_gt_atTop (0 : ℝ)] with frequency referenceSmall frequencyPositive
  intro orbit sectionTime phase dipoleAngle threshold scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path factorPositive index nonterminal finish finishInside
  dsimp only
  intro small origin profile exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let seed := changed.seed (index.val + 1)
  let size := fun time => |unstableShape motion time index| + |stableShape motion time index|
  have shapeContinuous := path.shape_continuousOn_of_small factorPositive index finishInside small
  have sizeContinuous : ContinuousOn size (Icc 0 finish) := shapeContinuous.1.abs.add shapeContinuous.2.abs
  have omegaPositive := changed.omega_pos frequencyPositive (by linarith only [ratioBound] : 0 < scales.ratio) (index.val + 1)
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive (by linarith only [ratioBound]) _
  have referenceBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < radius / 8 := by
    have bound := referenceSmall prepared time ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ index
    linarith only [bound, abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  have initialSmall : size 0 < radius := by
    have positiveInitial : positiveHalfDiagonal motion 0 index = positiveHalfDiagonal prepared.reference 0 index := by
      simp only [motion, positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
    have negativeInitial : negativeHalfDiagonal motion 0 index = negativeHalfDiagonal prepared.reference 0 index := by
      simp only [motion, negativeHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
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
    have normBound : ‖Section6.localNormalFormChart graph coordinate first -
        Section6.localNormalFormChart graph coordinate second‖ ≤
        |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).1| +
        |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    have atTime := profile time inside
    have exposureAt : seed * Real.exp (growth * (time - origin)) ≤ endpoint :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le).trans exposure
    have profileBound : |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).1| +
        |(Section6.localNormalFormChart graph coordinate first - Section6.localNormalFormChart graph coordinate second).2| ≤ magnitude * endpoint := by
      apply atTime.trans
      simpa only [seed, growth, changed, mul_assoc] using mul_le_mul_of_nonneg_left exposureAt magnitudeNonnegative
    have physical := distance.trans (mul_le_mul_of_nonneg_left (normBound.trans profileBound) (zero_le_one.trans inverseOne))
    have firstTriangle := abs_sub_abs_le_abs_sub first.1 second.1
    have secondTriangle := abs_sub_abs_le_abs_sub first.2 second.2
    have reference := referenceBound time inside
    change size time < radius / 2
    dsimp only [first, second, size] at physical firstTriangle secondTriangle
    nlinarith only [physical, firstTriangle, secondTriangle, reference, endpointBudget, radiusPositive]
  have confined := strictly_negative_of_prefix_improvement (sizeContinuous.sub continuousOn_const)
    (sub_neg.mpr initialSmall) (by
      intro time inside prefixControl
      exact sub_neg.mpr ((improve time inside (sub_nonpos.mp (prefixControl time ⟨inside.1, le_rfl⟩))).trans
        (half_lt_self radiusPositive)))
  intro time inside
  have bound := improve time inside (sub_neg.mp (confined time inside)).le
  exact bound.trans_le ((by linarith only [radiusPositive] : radius / 2 ≤ radius).trans radiusRequested)

end EulerNonuniqueness.Paper
