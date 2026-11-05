import EulerNonuniqueness.Section3.MovingCentroidGaugeChartedEquation
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialData
import EulerNonuniqueness.Section3.FiniteMovingPatchArea
import EulerNonuniqueness.Section3.DiskStationaryArea

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeAreaHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeAreaC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem MovingMaterialPatch.domain_area_eq_radius_sq_contourArea (path : MovingMaterialPatch) (time : ℝ) :
    volume.real (path.domain time) = path.radius ^ 2 * contourAreaFunctional (path.shape time) := by
  have identity := integral_similarityPatchDomain (path.center time) path.radius_positive
    (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) (fun _ => (1 : ℝ))
  have areaIdentity : volume.real (path.domain time) =
      path.radius ^ 2 * (volume (nearCircleInterior (path.shape time) (path.nearby time))).toReal := by
    simpa only [MovingMaterialPatch.domain, setIntegral_const, Measure.real,
      Measure.restrict_apply_univ, smul_eq_mul, mul_one] using identity
  rw [← contourAreaFunctional_eq_domain_area (path.shape time) (path.nearby time)] at areaIdentity
  exact areaIdentity

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem shape_area_eq_pi_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (marginPositive : 0 < margin) {horizon time : ℝ}
    (inside : time ∈ Icc 0 horizon) (beforeFinal : horizon < forwardHorizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count) : contourAreaFunctional ((trajectory.curve time).2.2 index) = Real.pi := by
  have areaConserved := trajectory.movingFamily.domain_area_eq_initial inside
    (fun _ => neg_neg_of_pos trajectory.backward_positive) (fun _ => beforeFinal)
    (fun current currentInside => trajectory.movingFamily_material_equation_of_margin marginPositive
      ⟨(neg_neg_of_pos trajectory.backward_positive).trans_le currentInside.1,
        currentInside.2.trans_lt beforeFinal⟩ (safe current currentInside)) index
  have areaInitial : volume.real ((trajectory.movingPatch index).domain 0) =
      Real.pi * configuration.radius index ^ 2 :=
    trajectory.movingPatch_area_initial_circle initialCircles index
  have areaCurrent := (trajectory.movingPatch index).domain_area_eq_radius_sq_contourArea time
  have identity : configuration.radius index ^ 2 * contourAreaFunctional ((trajectory.curve time).2.2 index) =
      Real.pi * configuration.radius index ^ 2 :=
    areaCurrent.symm.trans (areaConserved.trans areaInitial)
  have radiusPositive : 0 < configuration.radius index ^ 2 := sq_pos_of_pos (configuration.radius_pos index)
  nlinarith

theorem chartCoordinate_area_eq_pi_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (marginPositive : 0 < margin) {horizon time : ℝ}
    (inside : time ∈ Icc 0 horizon) (beforeFinal : horizon < forwardHorizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count)
    (rightInverse : diskStationaryChart (trajectory.chartCoordinate index time) = (trajectory.curve time).2.2 index) :
    diskStationaryArea (trajectory.chartCoordinate index time) = Real.pi := by
  rw [diskStationaryArea, rightInverse]
  exact trajectory.shape_area_eq_pi_of_margin initialCircles marginPositive inside beforeFinal safe index

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
