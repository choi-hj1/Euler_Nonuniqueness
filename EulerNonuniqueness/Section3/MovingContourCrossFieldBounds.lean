import EulerNonuniqueness.Section3.MovingContourStateGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingCrossBoundHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingCrossBoundC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.movingStateAdmissible_shapes_bounded {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (shapeSmall : shapeRadius ≤ 1) {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) (index : Fin count) :
    ‖state.2.2 index‖ ≤ 3 := by
  have bound := PeriodicC1HolderHalf.norm_le_radius_add_two (state.2.2 index) (inside.2.1 index)
  linarith

theorem FiniteContourConfiguration.movingStateAdmissible_centers_separated {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (first second : Fin count) (distinct : first ≠ second) :
    3 * (configuration.radius first + configuration.radius second) < ‖state.2.1 first - state.2.1 second‖ := by
  linarith [inside.2.2 first second distinct]

theorem FiniteContourConfiguration.movingStateAdmissible_physical_separated {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (shapeSmall : shapeRadius ≤ 1) {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (first second : Fin count) (distinct : first ≠ second) (sourceLabel targetLabel : ℝ) :
    gap ≤ ‖(configuration.movingStatePhysicalContour state first).val.1 targetLabel -
      (configuration.movingStatePhysicalContour state second).val.1 sourceLabel‖ := by
  let instant := configuration.atMovingState state (configuration.movingStateAdmissible_centers_separated positive inside)
  have gapBound : gap ≤ instant.crossGap first second := by
    change gap ≤ ‖state.2.1 first - state.2.1 second‖ - 3 * (configuration.radius first + configuration.radius second)
    linarith [inside.2.2 first second distinct]
  exact gapBound.trans (instant.phasedPhysicalContour_separated (configuration.movingStatePhase state) state.2.2 first second
    (configuration.movingStateAdmissible_shapes_bounded shapeSmall inside first)
    (configuration.movingStateAdmissible_shapes_bounded shapeSmall inside second) sourceLabel targetLabel)

theorem FiniteContourConfiguration.movingPhysicalUniformBound_nonnegative {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound : ℝ} (nonnegative : 0 ≤ centerBound) :
    0 ≤ configuration.movingPhysicalUniformBound centerBound := by
  have sumNonnegative : 0 ≤ ∑ index, configuration.radius index :=
    Finset.sum_nonneg (fun index _ => (configuration.radius_pos index).le)
  unfold FiniteContourConfiguration.movingPhysicalUniformBound
  positivity

theorem FiniteContourConfiguration.movingCross_uniform_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (shapeSmall : shapeRadius ≤ 1) {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (target source : Fin count) (distinct : target ≠ source) :
    ‖extendedCrossContourVelocity (configuration.movingStatePhysicalContour state target)
      (configuration.movingStatePhysicalContour state source)‖ ≤
      4 * crossContourPhaseBound (configuration.movingPhysicalUniformBound centerBound) gap *
        configuration.movingPhysicalUniformBound centerBound :=
  extendedCrossContourVelocity_uniform_norm_bound _ _ positive
    (configuration.movingStateAdmissible_physical_separated positive shapeSmall inside target source distinct)
    (configuration.movingStatePhysicalContour_norm_bound state inside.1
      (configuration.movingStateAdmissible_shapes_bounded shapeSmall inside) target)
    (configuration.movingStatePhysicalContour_norm_bound state inside.1
      (configuration.movingStateAdmissible_shapes_bounded shapeSmall inside) source)

theorem FiniteContourConfiguration.movingCross_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (centerNonnegative : 0 ≤ centerBound) (shapeSmall : shapeRadius ≤ 1)
    {first second : MovingContourState count}
    (firstInside : first ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (secondInside : second ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (target source : Fin count) (distinct : target ≠ source) :
    ‖extendedCrossContourVelocity (configuration.movingStatePhysicalContour first target)
        (configuration.movingStatePhysicalContour first source) -
      extendedCrossContourVelocity (configuration.movingStatePhysicalContour second target)
        (configuration.movingStatePhysicalContour second source)‖ ≤
      (crossContourIntegrandLipschitzBound (configuration.movingPhysicalUniformBound centerBound) gap / 2) *
        (configuration.movingPhysicalLipschitzConstant target + configuration.movingPhysicalLipschitzConstant source) *
          ‖first - second‖ := by
  have firstBound := configuration.movingStatePhysicalContour_norm_bound first firstInside.1
    (configuration.movingStateAdmissible_shapes_bounded shapeSmall firstInside)
  have secondBound := configuration.movingStatePhysicalContour_norm_bound second secondInside.1
    (configuration.movingStateAdmissible_shapes_bounded shapeSmall secondInside)
  have actual := extendedCrossContourVelocity_parameter_norm_bound
    (configuration.movingStatePhysicalContour first target) (configuration.movingStatePhysicalContour first source)
    (configuration.movingStatePhysicalContour second target) (configuration.movingStatePhysicalContour second source)
    positive (configuration.movingStateAdmissible_physical_separated positive shapeSmall firstInside target source distinct)
    (configuration.movingStateAdmissible_physical_separated positive shapeSmall secondInside target source distinct)
    (firstBound target) (firstBound source) (secondBound target) (secondBound source)
  have coefficientNonnegative := crossContourIntegrandLipschitzBound_nonneg
    (configuration.movingPhysicalUniformBound_nonnegative centerNonnegative) positive
  have targetBound := configuration.movingStatePhysicalContour_parameter_norm_bound first second
    (configuration.movingStateAdmissible_shapes_bounded shapeSmall secondInside) target
  have sourceBound := configuration.movingStatePhysicalContour_parameter_norm_bound first second
    (configuration.movingStateAdmissible_shapes_bounded shapeSmall secondInside) source
  apply actual.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add targetBound sourceBound) (div_nonneg coefficientNonnegative (by norm_num))).trans_eq
  ring

theorem FiniteContourConfiguration.movingStateInversePhase_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : MovingContourState count) (index : Fin count) :
    ‖(((configuration.movingStatePhase first index)⁻¹ : Circle) : ℂ) -
      (((configuration.movingStatePhase second index)⁻¹ : Circle) : ℂ)‖ ≤
      |configuration.density index / 2| * ‖first - second‖ := by
  rw [Circle.coe_inv_eq_conj, Circle.coe_inv_eq_conj, ← map_sub, Complex.norm_conj]
  exact configuration.movingStatePhase_parameter_norm_bound first second index

end EulerNonuniqueness.Paper
