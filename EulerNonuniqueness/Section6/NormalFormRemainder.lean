import EulerNonuniqueness.Section6.LocalNormalForm

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem fiber_vanishing_quadratic_bound {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {error coefficient : ℝ × ℝ → Value} {graph : ℝ → ℝ}
    (graphContinuous : ContinuousAt graph 0) (graphZero : graph 0 = 0)
    (coefficientSmooth : ContDiffAt ℝ 1 coefficient 0) (coefficientZero : coefficient 0 = 0)
    (verticalDerivative : ∀ᶠ point in nhds (0 : ℝ × ℝ),
      HasDerivAt (fun stable => error (point.1, stable)) (coefficient point) point.2)
    (vanishing : ∀ᶠ unstable in nhds (0 : ℝ), error (unstable, graph unstable) = 0) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
      |unstable| + |stable| < radius →
      ‖error (unstable, stable)‖ ≤
        bound * |stable - graph unstable| * (|unstable| + |stable| + |graph unstable|) := by
  obtain ⟨bound, neighborhood, neighborhoodMem, lipschitz⟩ := coefficientSmooth.exists_lipschitzOnWith
  obtain ⟨ambientRadius, ambientPositive, ballInside⟩ := Metric.mem_nhds_iff.mp
    (inter_mem neighborhoodMem verticalDerivative)
  have zeroInside : (0 : ℝ × ℝ) ∈ Metric.ball 0 ambientRadius := by simpa using ambientPositive
  have graphSmall : ∀ᶠ unstable in nhds (0 : ℝ), |graph unstable| < ambientRadius / 2 := by
    have actual := graphContinuous.eventually
      (Metric.ball_mem_nhds (graph 0) (show 0 < ambientRadius / 2 by positivity))
    simpa only [Metric.mem_ball, graphZero, dist_zero_right, Real.norm_eq_abs] using actual
  obtain ⟨graphRadius, graphRadiusPositive, graphInside⟩ := Metric.mem_nhds_iff.mp
    (inter_mem graphSmall vanishing)
  refine ⟨bound, bound.coe_nonneg, min graphRadius (ambientRadius / 2), by positivity, ?_⟩
  intro unstable stable sizeBound
  have unstableSmall : |unstable| < min graphRadius (ambientRadius / 2) :=
    lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg stable)) sizeBound
  have stableSmall : |stable| < ambientRadius / 2 :=
    (lt_of_le_of_lt (le_add_of_nonneg_left (abs_nonneg unstable)) sizeBound).trans_le (min_le_right _ _)
  have graphBounds := graphInside (show unstable ∈ Metric.ball (0 : ℝ) graphRadius by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using unstableSmall.trans_le (min_le_left _ _))
  have graphSmall : |graph unstable| < ambientRadius / 2 := graphBounds.1
  have unstableSmallAmbient := unstableSmall.trans_le (min_le_right _ _)
  have segmentAbs : ∀ current ∈ uIcc (graph unstable) stable,
      |current| ≤ max |graph unstable| |stable| := by
    intro current membership
    rw [mem_uIcc] at membership
    rcases membership with membership | membership
    · exact abs_le.mpr ⟨(neg_abs_le (graph unstable)).trans membership.1 |>.trans'
        (neg_le_neg (le_max_left _ _)), membership.2.trans ((le_abs_self stable).trans (le_max_right _ _))⟩
    · exact abs_le.mpr ⟨(neg_abs_le stable).trans membership.1 |>.trans'
        (neg_le_neg (le_max_right _ _)), membership.2.trans ((le_abs_self (graph unstable)).trans (le_max_left _ _))⟩
  have segmentInside : ∀ current ∈ uIcc (graph unstable) stable,
      (unstable, current) ∈ Metric.ball (0 : ℝ × ℝ) ambientRadius := by
    intro current membership
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    apply max_lt
    · linarith
    · exact (segmentAbs current membership).trans_lt (max_lt graphSmall stableSmall) |>.trans
        (by linarith)
  have derivative : ∀ current ∈ uIcc (graph unstable) stable,
      HasDerivWithinAt (fun stable => error (unstable, stable)) (coefficient (unstable, current))
        (uIcc (graph unstable) stable) current := by
    intro current membership
    exact (show HasDerivAt (fun stable => error (unstable, stable)) (coefficient (unstable, current)) current
      from (ballInside (segmentInside current membership)).2).hasDerivWithinAt
  have coefficientBound : ∀ current ∈ uIcc (graph unstable) stable,
      ‖coefficient (unstable, current)‖ ≤ (bound : ℝ) *
        (|unstable| + |stable| + |graph unstable|) := by
    intro current membership
    have localBound := (lipschitzOnWith_iff_norm_sub_le.mp lipschitz)
      (ballInside (segmentInside current membership)).1 (ballInside zeroInside).1
    rw [coefficientZero, sub_zero, sub_zero] at localBound
    apply localBound.trans
    apply mul_le_mul_of_nonneg_left _ bound.coe_nonneg
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    apply max_le
    · linarith [abs_nonneg stable, abs_nonneg (graph unstable)]
    · have currentBound := segmentAbs current membership
      have maximumBound : max |graph unstable| |stable| ≤ |stable| + |graph unstable| :=
        max_le (le_add_of_nonneg_left (abs_nonneg _)) (le_add_of_nonneg_right (abs_nonneg _))
      linarith [abs_nonneg unstable]
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le derivative coefficientBound
    (convex_uIcc (graph unstable) stable) left_mem_uIcc right_mem_uIcc
  rw [graphBounds.2, sub_zero, Real.norm_eq_abs] at estimate
  convert estimate using 1 <;> ring

def localNormalFormError (frequency : ℝ) (graph coordinate : ℝ → ℝ) (point : ℝ × ℝ) : ℝ × ℝ :=
  (deriv coordinate point.1 * (shapeChartVelocity frequency point).1 -
      2 * Real.sqrt 2 * frequency * coordinate point.1,
    (shapeChartVelocity frequency point).2 - deriv graph point.1 * (shapeChartVelocity frequency point).1 +
      2 * Real.sqrt 2 * frequency * (point.2 - graph point.1))

def localNormalFormCoefficient (frequency : ℝ) (graph coordinate : ℝ → ℝ) (point : ℝ × ℝ) : ℝ × ℝ :=
  (deriv coordinate point.1 * (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).1,
    (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).2 -
      deriv graph point.1 * (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).1 +
      2 * Real.sqrt 2 * frequency)

theorem scalar_deriv_contDiffAt_one {function : ℝ → ℝ}
    (smooth : ContDiffAt ℝ 2 function 0) : ContDiffAt ℝ 1 (deriv function) 0 := by
  exact (smooth.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem localNormalFormCoefficient_regular (frequency : ℝ) {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ContDiffAt ℝ 1 (localNormalFormCoefficient frequency graph coordinate) 0 ∧
      localNormalFormCoefficient frequency graph coordinate 0 = 0 := by
  have fieldPartial : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ => fderiv ℝ (shapeChartVelocity frequency) point (0, 1)) 0 :=
    ((shapeChartVelocity_contDiffAt frequency).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have graphPartial : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => deriv graph point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := deriv graph) 0 (scalar_deriv_contDiffAt_one graphSmooth) contDiffAt_fst
  have coordinatePartial : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => deriv coordinate point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := deriv coordinate) 0
      (scalar_deriv_contDiffAt_one coordinateSmooth) contDiffAt_fst
  constructor
  · exact (coordinatePartial.mul fieldPartial.fst).prodMk
      ((fieldPartial.snd.sub (graphPartial.mul fieldPartial.fst)).add contDiffAt_const)
  · simp [localNormalFormCoefficient, graphDerivative.deriv, coordinateDerivative.deriv,
      shapeChartVelocity_fderiv]

theorem localNormalFormError_vertical_derivative (frequency : ℝ) (graph coordinate : ℝ → ℝ) :
    ∀ᶠ point in nhds (0 : ℝ × ℝ), HasDerivAt
      (fun stable => localNormalFormError frequency graph coordinate (point.1, stable))
      (localNormalFormCoefficient frequency graph coordinate point) point.2 := by
  have smoothEventually := (shapeChartVelocity_contDiffAt frequency).eventually (by norm_num)
  filter_upwards [smoothEventually] with point smooth
  have path : HasDerivAt (fun stable : ℝ => (point.1, stable)) ((0 : ℝ), (1 : ℝ)) point.2 :=
    (hasDerivAt_const point.2 point.1).prodMk (hasDerivAt_id point.2)
  have composed : HasDerivAt (fun stable : ℝ => shapeChartVelocity frequency (point.1, stable))
      (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)) point.2 :=
    HasFDerivAt.comp_hasDerivAt (l := shapeChartVelocity frequency)
      (l' := fderiv ℝ (shapeChartVelocity frequency) point) point.2
      (smooth.differentiableAt (by norm_num)).hasFDerivAt path
  have firstComponent : HasDerivAt (fun stable : ℝ => (shapeChartVelocity frequency (point.1, stable)).1)
      (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).1 point.2 :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (l' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      point.2 (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt composed
  have secondComponent : HasDerivAt (fun stable : ℝ => (shapeChartVelocity frequency (point.1, stable)).2)
      (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).2 point.2 :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.snd) (l' := ContinuousLinearMap.snd ℝ ℝ ℝ)
      point.2 (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt composed
  have first := (firstComponent.const_mul (deriv coordinate point.1)).sub_const
    (2 * Real.sqrt 2 * frequency * coordinate point.1)
  have linear : HasDerivAt (fun stable : ℝ => 2 * Real.sqrt 2 * frequency * (stable - graph point.1))
      (2 * Real.sqrt 2 * frequency) point.2 := by
    simpa using ((hasDerivAt_id point.2).sub_const (graph point.1)).const_mul (2 * Real.sqrt 2 * frequency)
  have second := (secondComponent.sub (firstComponent.const_mul (deriv graph point.1))).add linear
  exact first.prodMk second

theorem localNormalForm_stable_factor_exists (frequency : ℝ) (frequencyNonzero : frequency ≠ 0) :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
        |unstable| + |stable| < radius →
        |(localNormalFormError frequency graph coordinate (unstable, stable)).1| +
          |(localNormalFormError frequency graph coordinate (unstable, stable)).2| ≤
          bound * |stable - graph unstable| * (|unstable| + |stable| + |graph unstable|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, normalForm⟩ := localNormalForm_on_separatrix_exists frequency frequencyNonzero
  have coefficientRegular := localNormalFormCoefficient_regular frequency
    (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth graphDerivative coordinateDerivative
  have vanishing : ∀ᶠ unstable in nhds (0 : ℝ),
      localNormalFormError frequency graph coordinate (unstable, graph unstable) = 0 := by
    filter_upwards [normalForm] with unstable identities
    unfold localNormalFormError
    rw [identities.1, identities.2]
    simp
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fiber_vanishing_quadratic_bound graphAnalytic.continuousAt graphZero coefficientRegular.1 coefficientRegular.2
      (localNormalFormError_vertical_derivative frequency graph coordinate) vanishing
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, 2 * bound, by positivity, radius, radiusPositive, ?_⟩
  intro unstable stable sizeBound
  have boundAtPoint := estimate unstable stable sizeBound
  have firstBound := (norm_fst_le (localNormalFormError frequency graph coordinate (unstable, stable))).trans boundAtPoint
  have secondBound := (norm_snd_le (localNormalFormError frequency graph coordinate (unstable, stable))).trans boundAtPoint
  simp only [Real.norm_eq_abs] at firstBound secondBound
  nlinarith

theorem localNormalForm_quadratic_stable_remainder_exists (frequency : ℝ) (frequencyNonzero : frequency ≠ 0) :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
        |unstable| + |stable| < radius →
        |(localNormalFormError frequency graph coordinate (unstable, stable)).1| +
          |(localNormalFormError frequency graph coordinate (unstable, stable)).2| ≤
          bound * |stable - graph unstable| * (|coordinate unstable| + |stable - graph unstable|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
      localNormalForm_stable_factor_exists frequency frequencyNonzero
  obtain ⟨graphBound, graphBoundPositive, graphEstimate⟩ := graphDerivative.isBigO_sub.exists_pos
  obtain ⟨inverseBound, inverseBoundPositive, inverseEstimate⟩ :=
    (coordinateDerivative.isBigO_sub_rev (by norm_num)).exists_pos
  have comparison : ∀ᶠ unstable in nhds (0 : ℝ),
      |graph unstable| ≤ graphBound * |unstable| ∧ |unstable| ≤ inverseBound * |coordinate unstable| := by
    filter_upwards [graphEstimate.bound, inverseEstimate.bound] with unstable graphEstimate inverseEstimate
    simpa only [graphZero, coordinateZero, sub_zero, Real.norm_eq_abs] using And.intro graphEstimate inverseEstimate
  obtain ⟨comparisonRadius, comparisonRadiusPositive, comparisonInside⟩ := Metric.mem_nhds_iff.mp comparison
  let sizeConstant := (1 + 2 * graphBound) * inverseBound + 1
  have sizeConstantPositive : 0 < sizeConstant := by dsimp [sizeConstant]; positivity
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, bound * sizeConstant, by positivity, min radius comparisonRadius, by positivity, ?_⟩
  intro unstable stable sizeBound
  have comparison := comparisonInside (show unstable ∈ Metric.ball (0 : ℝ) comparisonRadius by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg stable)) sizeBound).trans_le (min_le_right _ _))
  have originalBound := estimate unstable stable (sizeBound.trans_le (min_le_left _ _))
  have stableTriangle : |stable| ≤ |stable - graph unstable| + |graph unstable| := by
    simpa only [sub_add_cancel] using abs_add (stable - graph unstable) (graph unstable)
  have graphSize : |unstable| + 2 * |graph unstable| ≤
      ((1 + 2 * graphBound) * inverseBound) * |coordinate unstable| := by
    have amplified := mul_le_mul_of_nonneg_left comparison.2 (show 0 ≤ 1 + 2 * graphBound by positivity)
    nlinarith [comparison.1]
  have sizeComparison : |unstable| + |stable| + |graph unstable| ≤
      sizeConstant * (|coordinate unstable| + |stable - graph unstable|) := by
    have positiveProduct : 0 ≤ ((1 + 2 * graphBound) * inverseBound) * |stable - graph unstable| := by positivity
    dsimp [sizeConstant]
    nlinarith [abs_nonneg (coordinate unstable)]
  exact originalBound.trans (by
    convert mul_le_mul_of_nonneg_left sizeComparison
      (mul_nonneg boundNonnegative (abs_nonneg (stable - graph unstable))) using 1 <;> ring)

end EulerNonuniqueness.Section6
