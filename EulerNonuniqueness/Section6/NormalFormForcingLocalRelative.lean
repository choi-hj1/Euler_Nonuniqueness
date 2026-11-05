import EulerNonuniqueness.Section6.RelativeNormalFormForcingOperator
import EulerNonuniqueness.General.RealDerivativeUniformBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem sameGraph_referenceStraightenedForcing_exists_local_relative_bound
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ),
    |unstableShape first time index| ≤ radius → |unstableShape second time index| ≤ radius →
    ∀ leading : ℝ × ℝ,
    ‖referenceStraightenedForcing scales first graph coordinate index time -
        referenceStraightenedForcing scales second graph coordinate index time - leading‖ ≤
      constant * ‖referencePointShapeForcing scales first time index -
        referencePointShapeForcing scales second time index - leading‖ +
      constant * |unstableShape second time index| * ‖leading‖ +
      constant * |unstableShape first time index - unstableShape second time index| *
        ‖referencePointShapeForcing scales first time index‖ := by
  obtain ⟨graphRadius, graphPositive, graphConstant, graphOne, graphBound, graphLip⟩ :=
    EulerNonuniqueness.General.exists_uniform_real_derivative_ball graphSmooth
  obtain ⟨coordinateRadius, coordinatePositive, coordinateConstant, coordinateOne, coordinateBound, coordinateLip⟩ :=
    EulerNonuniqueness.General.exists_uniform_real_derivative_ball coordinateSmooth
  let constant := 1 + coordinateConstant + graphConstant
  have graphNonnegative : 0 ≤ graphConstant := by linarith
  have coordinateNonnegative : 0 ≤ coordinateConstant := by linarith
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨min graphRadius coordinateRadius, lt_min graphPositive coordinatePositive, constant, constantOne, ?_⟩
  intro count scales first second index time firstSmall secondSmall leading
  let firstPoint := unstableShape first time index
  let secondPoint := unstableShape second time index
  have firstGraph : |firstPoint| ≤ graphRadius := firstSmall.trans (min_le_left _ _)
  have secondGraph : |secondPoint| ≤ graphRadius := secondSmall.trans (min_le_left _ _)
  have firstCoordinate : |firstPoint| ≤ coordinateRadius := firstSmall.trans (min_le_right _ _)
  have secondCoordinate : |secondPoint| ≤ coordinateRadius := secondSmall.trans (min_le_right _ _)
  have coefficientBound : 1 + |deriv coordinate secondPoint| + |deriv graph secondPoint| ≤ constant := by
    have firstBound := coordinateBound secondPoint secondCoordinate
    have secondBound := graphBound secondPoint secondGraph
    dsimp only [constant]
    linarith
  have coordinateDeviation : |deriv coordinate secondPoint - 1| ≤ coordinateConstant * |secondPoint| := by
    have actual := coordinateLip secondPoint 0 secondCoordinate (by simpa only [abs_zero] using coordinatePositive.le)
    simpa only [coordinateDerivative.deriv, sub_zero] using actual
  have graphDeviation : |deriv graph secondPoint| ≤ graphConstant * |secondPoint| := by
    have actual := graphLip secondPoint 0 secondGraph (by simpa only [abs_zero] using graphPositive.le)
    simpa only [graphDerivative.deriv, sub_zero] using actual
  have deviationBound : |deriv coordinate secondPoint - 1| + |deriv graph secondPoint| ≤ constant * |secondPoint| := by
    have sum := add_le_add coordinateDeviation graphDeviation
    dsimp only [constant]
    nlinarith [abs_nonneg secondPoint]
  have variationBound : |deriv coordinate firstPoint - deriv coordinate secondPoint| +
      |deriv graph firstPoint - deriv graph secondPoint| ≤ constant * |firstPoint - secondPoint| := by
    have sum := add_le_add (coordinateLip firstPoint secondPoint firstCoordinate secondCoordinate)
      (graphLip firstPoint secondPoint firstGraph secondGraph)
    dsimp only [constant]
    nlinarith [abs_nonneg (firstPoint - secondPoint)]
  have actual := referenceStraightenedForcing_relative_leading_bound scales first second graph coordinate index time leading
  apply actual.trans
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg _))
      (mul_le_mul_of_nonneg_right deviationBound (norm_nonneg leading)))
    (mul_le_mul_of_nonneg_right variationBound (norm_nonneg _))

end EulerNonuniqueness.Paper
