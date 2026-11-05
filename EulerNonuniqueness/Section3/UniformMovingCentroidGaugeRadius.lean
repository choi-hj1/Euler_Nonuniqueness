import EulerNonuniqueness.Section3.MovingCentroidGaugeUniformBounds

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance uniformMovingGaugeHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance uniformMovingGaugeC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance uniformMovingGaugeDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

theorem exists_uniform_moving_centroid_gauge_shape_radius :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ count : ℕ, ∀ configuration : FiniteContourConfiguration count,
      ∀ centerBound ≥ 0, ∀ gap > 0, ∃ fieldConstant bound : NNReal,
        LipschitzOnWith fieldConstant configuration.movingStateVectorField
          (configuration.movingStateAdmissible centerBound shapeRadius gap) ∧
        ∀ state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap,
          ‖configuration.movingStateVectorField state‖ ≤ bound := by
  obtain ⟨radius, radiusPositive, radiusSmall, constant, constantNonnegative, derivativeBound, derivativeDifference,
      _projectionBound, _projectionDifference⟩ := contourCentroidGauge_exists_local_uniform_bounds
  let shapeRadius : ℝ := min (radius / 2) (1 / (3 * Real.pi))
  have shapePositive : 0 < shapeRadius := lt_min (by positivity) (by positivity)
  have shapeLe : shapeRadius ≤ radius := (min_le_left _ _).trans (by linarith)
  have chordSmall : shapeRadius < 2 / (3 * Real.pi) :=
    (min_le_right _ _).trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  have shapeSmall : shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) :=
    lt_min (shapeLe.trans_lt radiusSmall) chordSmall
  have banachSmall : shapeRadius < min 1 (2 / (3 * Real.pi)) :=
    lt_min ((shapeSmall.trans_le (min_le_left _ _)).trans (by norm_num)) chordSmall
  have subset : closedBall standardCircleBanach shapeRadius ⊆ closedBall standardCircleBanach radius :=
    closedBall_subset_closedBall shapeLe
  have derivativeBoundSmall : ∀ data ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant := fun data member => derivativeBound data (subset member)
  have derivativeDifferenceSmall : ∀ first ∈ closedBall standardCircleBanach shapeRadius,
      ∀ second ∈ closedBall standardCircleBanach shapeRadius,
      ‖fderiv ℝ contourCentroidFunctional first - fderiv ℝ contourCentroidFunctional second‖ ≤
        constant * ‖first - second‖ :=
    fun first firstMember second secondMember => derivativeDifference first (subset firstMember) second (subset secondMember)
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro count configuration centerBound centerNonnegative gap gapPositive
  let fieldConstant : NNReal := ⟨configuration.movingGaugeLipschitzBound centerBound shapeRadius gap constant,
    (configuration.movingGaugeLipschitzBound_positive centerBound shapeRadius gap constantNonnegative).le⟩
  let bound : NNReal := ⟨configuration.movingGaugeUniformBound centerBound shapeRadius gap constant,
    (configuration.movingGaugeUniformBound_positive centerBound shapeRadius gap constantNonnegative).le⟩
  refine ⟨fieldConstant, bound,
    configuration.movingStateVectorField_lipschitzOn gapPositive centerNonnegative shapePositive.le banachSmall
      constantNonnegative derivativeBoundSmall derivativeDifferenceSmall, ?_⟩
  intro state inside
  exact configuration.movingStateVectorField_uniform_norm_bound gapPositive shapePositive.le banachSmall
    constantNonnegative derivativeBoundSmall inside

end EulerNonuniqueness.Paper
