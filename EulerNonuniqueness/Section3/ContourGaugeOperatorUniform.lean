import EulerNonuniqueness.Section3.ContourGaugeOperatorTaylor

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] centroidGaugeRegularityC1Space centroidGaugeRegularityDerivativeGroup
  centroidGaugeRegularityDerivativeSpace centroidGaugeRegularityOperatorGroup gaugeOperatorTaylorOperatorSpace

local instance gaugeOperatorUniformC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance gaugeOperatorUniformSecondGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem circleBasedCentroidProjection_exists_uniform_firstJet_bounds :
    ∃ radius > 0, radius ≤ 1 / 6 ∧ ∃ constant ≥ 1,
      (∀ base : PeriodicC1HolderHalf, ‖base‖ ≤ radius →
        ‖circleBasedCentroidProjection base‖ ≤ constant ∧
        ‖fderiv ℝ circleBasedCentroidProjection base‖ ≤ constant) ∧
      (∀ first second : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖second‖ ≤ radius →
        ‖circleBasedCentroidProjection first - circleBasedCentroidProjection second‖ ≤
          constant * ‖first - second‖) ∧
      ∀ base increment : PeriodicC1HolderHalf, ‖base‖ + ‖increment‖ ≤ radius →
        ‖circleBasedCentroidProjection (base + increment) - circleBasedCentroidProjection base -
          fderiv ℝ circleBasedCentroidProjection base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
  obtain ⟨gaugeRadius, gaugePositive, _, gaugeConstant, gaugeNonnegative, _, _, gaugeBound, gaugeDifference⟩ :=
    contourCentroidGauge_exists_local_uniform_bounds
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeNonnegative, derivativeBound, _⟩ :=
    EulerNonuniqueness.General.exists_closedBall_fderiv_bound_of_contDiffAt_two
      circleBasedCentroidProjection_contDiffAt_two
  obtain ⟨taylorRadius, taylorPositive, taylorConstant, taylorNonnegative, taylorBound⟩ :=
    circleBasedCentroidProjection_exists_uniform_quadratic_remainder
  let radius := min gaugeRadius (min derivativeRadius (min taylorRadius (1 / 6)))
  let constant := 1 + gaugeConstant + derivativeConstant + taylorConstant
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusGauge : radius ≤ gaugeRadius := min_le_left _ _
  have radiusDerivative : radius ≤ derivativeRadius :=
    (min_le_right _ _).trans (min_le_left _ _)
  have radiusTaylor : radius ≤ taylorRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusSmall : radius ≤ 1 / 6 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have gaugeMember (base : PeriodicC1HolderHalf) (bound : ‖base‖ ≤ radius) :
      standardCircleBanach + base ∈ closedBall standardCircleBanach gaugeRadius := by
    rw [mem_closedBall]
    with_reducible_and_instances
      rw [dist_eq_norm (standardCircleBanach + base) standardCircleBanach, add_sub_cancel_left]
      exact bound.trans radiusGauge
  have gaugeConstantLe : 1 + gaugeConstant ≤ constant := by dsimp [constant]; linarith
  have derivativeConstantLe : derivativeConstant ≤ constant := by dsimp [constant]; linarith
  have taylorConstantLe : taylorConstant ≤ constant := by dsimp [constant]; linarith
  refine ⟨radius, radiusPositive, radiusSmall, constant, by dsimp [constant]; linarith, ?_, ?_, ?_⟩
  · intro base bound
    exact ⟨(gaugeBound _ (gaugeMember base bound)).trans gaugeConstantLe,
      (derivativeBound base (mem_closedBall_zero_iff.mpr (bound.trans radiusDerivative))).trans derivativeConstantLe⟩
  · intro first second firstBound secondBound
    have estimate := gaugeDifference _ (gaugeMember first firstBound) _ (gaugeMember second secondBound)
    have constantLe : gaugeConstant ≤ constant := by dsimp [constant]; linarith
    unfold circleBasedCentroidProjection
    have actual : ‖(standardCircleBanach + first) - (standardCircleBanach + second)‖ = ‖first - second‖ := by
      rw [add_sub_add_left_eq_sub]
    rw [actual] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right constantLe (norm_nonneg _))
  · intro base increment bound
    exact (taylorBound base increment (bound.trans radiusTaylor)).trans
      (mul_le_mul_of_nonneg_right taylorConstantLe (sq_nonneg _))

end EulerNonuniqueness.Paper
