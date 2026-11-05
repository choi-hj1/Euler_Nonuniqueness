import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeEquation

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingChartedEquationHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingChartedEquationC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance movingChartedEquationOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

private theorem operator_norm_bound {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (operator : Space →L[ℝ] Space) (value : Space) : ‖operator value‖ ≤ ‖operator‖ * ‖value‖ :=
  operator.le_opNorm value

theorem diskStationaryChart_exists_inverse_ODE_radius :
    ∃ radius > 0, ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ < radius →
      diskStationaryChart (diskStationaryChartPartialHomeomorph.symm data) = data ∧
      HasFDerivAt diskStationaryChartPartialHomeomorph.symm
        (diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm data)) data := by
  obtain ⟨radius, positive, valid⟩ := Metric.eventually_nhds_iff.mp
    diskStationaryChart_eventually_inverse_derivative
  refine ⟨radius, positive, ?_⟩
  intro data small
  apply valid
  simpa only [dist_eq_norm data standardCircleBanach] using small

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

def chartCoordinate
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (index : Fin count) (time : ℝ) : PeriodicC1HolderHalf :=
  diskStationaryChartPartialHomeomorph.symm ((trajectory.curve time).2.2 index)

def chartForcing
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (index : Fin count) (time : ℝ) : PeriodicC1HolderHalf :=
  diskChartInverseDerivative (trajectory.chartCoordinate index time)
    (contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
      (configuration.movingStateExternalField (trajectory.curve time) index))

theorem chartCoordinate_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCentered : ∀ index, contourCentroidFunctional (initial.2.2 index) = 0)
    (marginPositive : 0 < margin) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (safe : margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count)
    (rightInverse : diskStationaryChart (trajectory.chartCoordinate index time) = (trajectory.curve time).2.2 index)
    (inverseDerivative : HasFDerivAt diskStationaryChartPartialHomeomorph.symm
      (diskChartInverseDerivative (trajectory.chartCoordinate index time)) ((trajectory.curve time).2.2 index)) :
    HasDerivAt (trajectory.chartCoordinate index)
      (configuration.density index • diskChartedEulerField (trajectory.chartCoordinate index time) +
        trajectory.chartForcing index time) time := by
  exact hasDerivAt_diskStationaryChart_inverse_of_equation
    (trajectory.shape_hasDerivAt_self_external initialCentered marginPositive inside safe index)
    rightInverse inverseDerivative

theorem exists_uniform_charted_equation_radius :
    ∃ radius > 0,
    ∀ (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial),
    (∀ index, contourCentroidFunctional (initial.2.2 index) = 0) →
    0 < margin → ∀ time ∈ Ioo (-backwardHorizon) forwardHorizon,
      margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ →
      ∀ index, ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
        diskStationaryChart (trajectory.chartCoordinate index time) = (trajectory.curve time).2.2 index ∧
        HasDerivAt (trajectory.chartCoordinate index)
          (configuration.density index • diskChartedEulerField (trajectory.chartCoordinate index time) +
            trajectory.chartForcing index time) time := by
  obtain ⟨radius, positive, valid⟩ := diskStationaryChart_exists_inverse_ODE_radius
  refine ⟨radius, positive, ?_⟩
  intro trajectory centered marginPositive time inside safe index small
  obtain ⟨rightInverse, inverseDerivative⟩ := valid ((trajectory.curve time).2.2 index) small
  exact ⟨rightInverse, trajectory.chartCoordinate_hasDerivAt centered marginPositive inside safe index rightInverse inverseDerivative⟩

theorem chartForcing_norm_bound
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (index : Fin count) (time : ℝ) :
    ‖trajectory.chartForcing index time‖ ≤
      ‖diskChartInverseDerivative (trajectory.chartCoordinate index time)‖ *
        ‖contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
          (configuration.movingStateExternalField (trajectory.curve time) index)‖ := by
  unfold chartForcing
  with_reducible
    exact operator_norm_bound (Space := PeriodicC1HolderHalf)
      (diskChartInverseDerivative (trajectory.chartCoordinate index time))
      (contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
        (configuration.movingStateExternalField (trajectory.curve time) index))

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
