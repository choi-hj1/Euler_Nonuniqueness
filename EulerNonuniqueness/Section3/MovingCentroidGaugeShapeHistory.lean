import EulerNonuniqueness.Section3.MovingCentroidGaugeNeutralHistory
import EulerNonuniqueness.Section3.DiskPhysicalSpectralShapeBound

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance movingGaugeShapeHistoryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem exists_uniform_spectral_shape_history_radius :
    ∃ radius > 0, ∃ neutralConstant ≥ 1, ∃ shapeConstant ≥ 1,
      ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
        {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
        {initial : MovingContourState count}
        (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
          backwardHorizon forwardHorizon initial),
      (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
      ∀ horizon distance weight transverseRadius : ℝ, horizon < forwardHorizon →
      (∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
      ∀ (index : Fin count), 0 < distance → 0 ≤ weight → 0 ≤ transverseRadius →
      192 * (trajectory.movingFamily.patch index).radius ≤ distance →
      (∀ current ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index,
        ∀ position ∈ (trajectory.movingFamily.patch source).domain current,
        distance ≤ ‖(trajectory.movingFamily.patch index).center current - position‖) →
      (∀ current ∈ Icc 0 horizon, (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
        ((trajectory.movingFamily.patch index).center current) position) ≤ weight) →
      (∀ current ∈ Icc 0 horizon, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < radius) →
      (∀ current ∈ Icc 0 horizon,
        ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index current)‖ ≤ transverseRadius) →
      ∀ time ∈ Icc 0 horizon,
        ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ ≤
          shapeConstant * (neutralConstant *
            (|configuration.density index| * transverseRadius ^ 2 + weight * transverseRadius) * time + transverseRadius) := by
  obtain ⟨historyRadius, historyPositive, neutralConstant, neutralOne, history⟩ :=
    exists_uniform_spectral_neutral_history_radius
  obtain ⟨shapeRadius, shapePositive, shapeConstant, shapeOne, shapes⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_area_shape_bound
  refine ⟨min historyRadius shapeRadius, lt_min historyPositive shapePositive,
    neutralConstant, neutralOne, shapeConstant, shapeOne, ?_⟩
  intro count configuration centerBound shapeRadiusBound gap margin backwardHorizon forwardHorizon initial
    trajectory initialCircles initialClock marginPositive horizon distance weight transverseRadius beforeFinal safe
    index distancePositive weightNonnegative transverseNonnegative small separated weightBound nearby transverseBound
    time inside
  have neutral := history trajectory initialCircles initialClock marginPositive
    horizon distance weight transverseRadius beforeFinal safe index distancePositive weightNonnegative
    transverseNonnegative small separated weightBound
    (fun current member => (nearby current member).trans_le (min_le_left _ _)) transverseBound time inside
  have area := trajectory.shape_area_eq_pi_of_margin initialCircles marginPositive inside beforeFinal safe index
  have shape := shapes ((trajectory.curve time).2.2 index)
    ((nearby time inside).trans_le (min_le_right _ _)) area
  have projected := transverseBound time inside
  unfold spectralCoordinate at neutral projected
  generalize dataEq : (trajectory.curve time).2.2 index = data at shape neutral projected ⊢
  generalize neutralEq : diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data) = neutralValue
    at shape neutral
  generalize projectedEq : diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data) = projectedValue
    at shape projected
  exact shape.trans (mul_le_mul_of_nonneg_left (add_le_add neutral projected) (by linarith))

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
