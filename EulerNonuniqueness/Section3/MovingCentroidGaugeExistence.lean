import EulerNonuniqueness.Section3.MovingCentroidGaugeUniformBounds
import EulerNonuniqueness.General.CutoffODEFamily

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeExistenceHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeExistenceC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance movingGaugeExistenceDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

theorem FiniteContourConfiguration.exists_movingStateVectorField_uniform_bounds {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∃ fieldConstant bound : NNReal,
        LipschitzOnWith fieldConstant configuration.movingStateVectorField
          (configuration.movingStateAdmissible centerBound shapeRadius gap) ∧
        ∀ state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap,
          ‖configuration.movingStateVectorField state‖ ≤ bound := by
  obtain ⟨radius, radiusPositive, radiusSmall, constant, constantNonnegative, derivativeBound, derivativeDifference, _projectionBound, _projectionDifference⟩ :=
    contourCentroidGauge_exists_local_uniform_bounds
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
      ‖fderiv ℝ contourCentroidFunctional first - fderiv ℝ contourCentroidFunctional second‖ ≤ constant * ‖first - second‖ :=
    fun first firstMember second secondMember => derivativeDifference first (subset firstMember) second (subset secondMember)
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive
  let fieldConstant : NNReal := ⟨configuration.movingGaugeLipschitzBound centerBound shapeRadius gap constant,
    (configuration.movingGaugeLipschitzBound_positive centerBound shapeRadius gap constantNonnegative).le⟩
  let bound : NNReal := ⟨configuration.movingGaugeUniformBound centerBound shapeRadius gap constant,
    (configuration.movingGaugeUniformBound_positive centerBound shapeRadius gap constantNonnegative).le⟩
  refine ⟨fieldConstant, bound, configuration.movingStateVectorField_lipschitzOn gapPositive centerNonnegative
    shapePositive.le banachSmall constantNonnegative derivativeBoundSmall derivativeDifferenceSmall, ?_⟩
  intro state inside
  exact configuration.movingStateVectorField_uniform_norm_bound gapPositive shapePositive.le banachSmall
    constantNonnegative derivativeBoundSmall inside

theorem FiniteContourConfiguration.exists_jointly_continuous_moving_centroid_gauge_cutoff_flow {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ horizon ≥ 0,
      ∃ flow : MovingContourState count → ℝ → MovingContourState count,
        (∀ initial, flow initial 0 = initial) ∧
        Continuous (fun point : MovingContourState count × ℝ => flow point.1 point.2) ∧
        (∀ initial time, time ∈ Icc 0 horizon → HasDerivWithinAt (flow initial)
          (EulerNonuniqueness.General.distanceFieldCutoff
            (configuration.movingStateAdmissible centerBound shapeRadius gap) margin (flow initial time) •
              configuration.movingStateVectorField (flow initial time)) (Icc 0 horizon) time) ∧
        ∀ initial time, time ∈ Icc 0 horizon →
          margin ≤ infDist (flow initial time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ →
          HasDerivWithinAt (flow initial) (configuration.movingStateVectorField (flow initial time)) (Icc 0 horizon) time := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, bounds⟩ := configuration.exists_movingStateVectorField_uniform_bounds
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive horizon horizonNonnegative
  obtain ⟨fieldConstant, bound, lipschitz, bounded⟩ := bounds centerBound centerNonnegative gap gapPositive
  obtain ⟨flow, initialIdentity, jointContinuous, cutoffEquation, trueEquation, _stability⟩ :=
    EulerNonuniqueness.General.exists_jointly_continuous_cutoff_ODE_family configuration.movingStateVectorField
      (configuration.movingStateAdmissible centerBound shapeRadius gap) marginPositive fieldConstant bound
      lipschitz bounded horizonNonnegative
  exact ⟨flow, initialIdentity, jointContinuous, cutoffEquation, trueEquation⟩

end EulerNonuniqueness.Paper
