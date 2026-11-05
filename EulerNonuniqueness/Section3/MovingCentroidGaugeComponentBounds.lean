import EulerNonuniqueness.Section3.MovingContourRawFieldBounds
import EulerNonuniqueness.General.OperatorApplicationDifference
import EulerNonuniqueness.Section3.ContourCentroidGaugePointBounds

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeComponentHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeComponentC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance movingGaugeComponentDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)
local instance movingGaugeComponentOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem norm_unit_complex_mul_sub_mul_le (firstPhase secondPhase : Circle) (first second : ℂ) :
    ‖(firstPhase : ℂ) * first - (secondPhase : ℂ) * second‖ ≤
      ‖first - second‖ + ‖(firstPhase : ℂ) - (secondPhase : ℂ)‖ * ‖second‖ := by
  have identity : (firstPhase : ℂ) * first - (secondPhase : ℂ) * second =
      (firstPhase : ℂ) * (first - second) + ((firstPhase : ℂ) - (secondPhase : ℂ)) * second := by ring
  rw [identity]
  simpa only [norm_mul, Circle.norm_coe, one_mul] using
    norm_add_le ((firstPhase : ℂ) * (first - second)) (((firstPhase : ℂ) - (secondPhase : ℂ)) * second)

theorem FiniteContourConfiguration.movingStateAdmissible_shape_mem_closedBall {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) (index : Fin count) :
    state.2.2 index ∈ closedBall standardCircleBanach shapeRadius := by
  change dist (state.2.2 index) standardCircleBanach ≤ shapeRadius
  rw [dist_eq_norm (state.2.2 index) standardCircleBanach]
  exact inside.2.1 index

theorem FiniteContourConfiguration.movingStateVectorField_component_norm_bounds {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap constant : ℝ}
    (positive : 0 < gap) (shapeNonnegative : 0 ≤ shapeRadius)
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi))) (constantNonnegative : 0 ≤ constant)
    (derivativeBound : ∀ data ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant)
    {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) (index : Fin count) :
    ‖(configuration.movingStateVectorField state).2.1 index‖ ≤ configuration.radius index * constant *
        |configuration.movingRawNormBound centerBound shapeRadius gap index| ∧
      ‖(configuration.movingStateVectorField state).2.2 index‖ ≤ (1 + constant) *
        |configuration.movingRawNormBound centerBound shapeRadius gap index| := by
  have actualRaw := (configuration.movingStateRawField_uniform_norm_bound positive shapeNonnegative shapeSmall inside index).trans
    (le_abs_self _)
  have actualDerivative := derivativeBound (state.2.2 index) (configuration.movingStateAdmissible_shape_mem_closedBall inside index)
  constructor
  · change ‖configuration.radius index • ((configuration.movingStatePhase state index : ℂ) *
      (fderiv ℝ contourCentroidFunctional (state.2.2 index)) (configuration.movingStateRawField state index))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (configuration.radius_pos index), norm_mul, Circle.norm_coe, one_mul]
    have applicationBound := ((fderiv ℝ contourCentroidFunctional (state.2.2 index)).le_opNorm
      (configuration.movingStateRawField state index)).trans
        (mul_le_mul actualDerivative actualRaw (norm_nonneg _) constantNonnegative)
    exact (mul_le_mul_of_nonneg_left applicationBound (configuration.radius_pos index).le).trans_eq (by ring)
  · change ‖contourCentroidGaugeProjection (state.2.2 index) (configuration.movingStateRawField state index)‖ ≤ _
    exact contourCentroidGaugeProjection_apply_norm_bound (state.2.2 index) (configuration.movingStateRawField state index)
      constantNonnegative actualDerivative actualRaw

theorem FiniteContourConfiguration.movingStateVectorField_component_parameter_bounds {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap constant : ℝ}
    (positive : 0 < gap) (centerNonnegative : 0 ≤ centerBound) (shapeNonnegative : 0 ≤ shapeRadius)
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi))) (constantNonnegative : 0 ≤ constant)
    (derivativeBound : ∀ data ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant)
    (derivativeDifference : ∀ first ∈ closedBall standardCircleBanach shapeRadius,
      ∀ second ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional first - fderiv ℝ contourCentroidFunctional second‖ ≤ constant * ‖first - second‖)
    {first second : MovingContourState count}
    (firstInside : first ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (secondInside : second ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) (index : Fin count) :
    ‖(configuration.movingStateVectorField first).2.1 index - (configuration.movingStateVectorField second).2.1 index‖ ≤
        configuration.radius index * (constant * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
          constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| +
          |configuration.density index / 2| * constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|) * ‖first - second‖ ∧
      ‖(configuration.movingStateVectorField first).2.2 index - (configuration.movingStateVectorField second).2.2 index‖ ≤
        ((1 + constant) * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
          constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|) * ‖first - second‖ := by
  have firstMember := configuration.movingStateAdmissible_shape_mem_closedBall firstInside index
  have secondMember := configuration.movingStateAdmissible_shape_mem_closedBall secondInside index
  have firstDerivative := derivativeBound (first.2.2 index) firstMember
  have secondDerivative := derivativeBound (second.2.2 index) secondMember
  have operatorDifference := (derivativeDifference (first.2.2 index) firstMember (second.2.2 index) secondMember).trans
    (mul_le_mul_of_nonneg_left (movingContourState_shape_norm_sub_le first second index) constantNonnegative)
  have rawBound := (configuration.movingStateRawField_uniform_norm_bound positive shapeNonnegative shapeSmall secondInside index).trans (le_abs_self _)
  have rawDifference := (configuration.movingStateRawField_parameter_norm_bound positive centerNonnegative shapeNonnegative shapeSmall firstInside secondInside index).trans
    (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg (first - second)))
  have applicationBound : ‖(fderiv ℝ contourCentroidFunctional (second.2.2 index))
      (configuration.movingStateRawField second index)‖ ≤ constant * |configuration.movingRawNormBound centerBound shapeRadius gap index| :=
    ((fderiv ℝ contourCentroidFunctional (second.2.2 index)).le_opNorm _).trans
      (mul_le_mul secondDerivative rawBound (norm_nonneg _) constantNonnegative)
  have applicationDifference : ‖(fderiv ℝ contourCentroidFunctional (first.2.2 index)) (configuration.movingStateRawField first index) -
      (fderiv ℝ contourCentroidFunctional (second.2.2 index)) (configuration.movingStateRawField second index)‖ ≤
      (constant * |configuration.movingRawLipschitzBound centerBound shapeRadius gap index| +
        constant * |configuration.movingRawNormBound centerBound shapeRadius gap index|) * ‖first - second‖ := by
    apply (EulerNonuniqueness.General.norm_operator_application_sub_le (Scalar := ℝ)
      (Domain := PeriodicC1HolderHalf) (Range := ℂ)
      (fderiv ℝ contourCentroidFunctional (first.2.2 index)) (fderiv ℝ contourCentroidFunctional (second.2.2 index))
      (configuration.movingStateRawField first index) (configuration.movingStateRawField second index)).trans
    exact (add_le_add (mul_le_mul firstDerivative rawDifference (norm_nonneg _) constantNonnegative)
      (mul_le_mul operatorDifference rawBound (norm_nonneg _) (by positivity))).trans_eq (by ring)
  constructor
  · change ‖configuration.radius index • ((configuration.movingStatePhase first index : ℂ) *
        (fderiv ℝ contourCentroidFunctional (first.2.2 index)) (configuration.movingStateRawField first index)) -
      configuration.radius index • ((configuration.movingStatePhase second index : ℂ) *
        (fderiv ℝ contourCentroidFunctional (second.2.2 index)) (configuration.movingStateRawField second index))‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (configuration.radius_pos index)]
    have phaseBound := configuration.movingStatePhase_parameter_norm_bound first second index
    have actual := norm_unit_complex_mul_sub_mul_le (configuration.movingStatePhase first index) (configuration.movingStatePhase second index)
      ((fderiv ℝ contourCentroidFunctional (first.2.2 index)) (configuration.movingStateRawField first index))
      ((fderiv ℝ contourCentroidFunctional (second.2.2 index)) (configuration.movingStateRawField second index))
    have combined := actual.trans (add_le_add applicationDifference
      (mul_le_mul phaseBound applicationBound (norm_nonneg _) (by positivity)))
    exact (mul_le_mul_of_nonneg_left combined (configuration.radius_pos index).le).trans_eq (by ring)
  · change ‖contourCentroidGaugeProjection (first.2.2 index) (configuration.movingStateRawField first index) -
      contourCentroidGaugeProjection (second.2.2 index) (configuration.movingStateRawField second index)‖ ≤ _
    have projectionNorm := (contourCentroidGaugeProjection_norm_bound (first.2.2 index)).trans (add_le_add_left firstDerivative 1)
    have projectionDifference := (contourCentroidGaugeProjection_difference_norm_bound (first.2.2 index) (second.2.2 index)).trans operatorDifference
    apply (EulerNonuniqueness.General.norm_operator_application_sub_le (Scalar := ℝ)
      (Domain := PeriodicC1HolderHalf) (Range := PeriodicC1HolderHalf)
      (contourCentroidGaugeProjection (first.2.2 index)) (contourCentroidGaugeProjection (second.2.2 index))
      (configuration.movingStateRawField first index) (configuration.movingStateRawField second index)).trans
    exact (add_le_add (mul_le_mul projectionNorm rawDifference (norm_nonneg _) (by positivity))
      (mul_le_mul projectionDifference rawBound (norm_nonneg _) (by positivity))).trans_eq (by ring)

end EulerNonuniqueness.Paper
