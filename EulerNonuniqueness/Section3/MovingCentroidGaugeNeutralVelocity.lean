import EulerNonuniqueness.Section3.MovingCanonicalSpectralForcing
import EulerNonuniqueness.Section3.CanonicalExteriorNeutralSpeed
import EulerNonuniqueness.Section3.MovingCentroidGaugeSpectralSelf
import EulerNonuniqueness.Section3.DiskSpectralScaledEquation

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

local instance movingGaugeNeutralVelocityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

theorem exists_uniform_spectral_neutral_velocity_radius :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
        {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
        {initial : MovingContourState count}
        (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
          backwardHorizon forwardHorizon initial),
      (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
      ∀ horizon time distance weight : ℝ, time ∈ Icc 0 horizon → horizon < forwardHorizon →
      (∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
      ∀ (index : Fin count) (positive : 0 < distance), 0 ≤ weight →
      192 * (trajectory.movingFamily.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
        distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time)
        ((trajectory.movingFamily.patch index).center time) position) ≤ weight →
      ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
      ∃ velocity : PeriodicC1HolderHalf,
        HasDerivAt (fun current => diskRelabelNeutralCLM (trajectory.spectralCoordinate index current)) velocity time ∧
        ‖velocity‖ ≤ constant *
          (|configuration.density index| * ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖ ^ 2 +
            weight * ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖) := by
  obtain ⟨speedRadius, speedPositive, constant, constantOne, speedBound⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_neutral_speed
  obtain ⟨coordinateRadius, coordinatePositive, coordinates⟩ :=
    diskPhysicalSpectralCoordinate_exists_radius speedPositive
  obtain ⟨equationRadius, equationPositive, equations⟩ := exists_uniform_spectral_equation_radius
  refine ⟨min coordinateRadius equationRadius, lt_min coordinatePositive equationPositive,
    constant, constantOne, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory initialCircles initialClock marginPositive horizon time distance weight inside beforeFinal safe
    index positive weightNonnegative small separated weightBound nearby
  have interior : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨(neg_neg_of_pos trajectory.backward_positive).trans_le inside.1, inside.2.trans_lt beforeFinal⟩
  obtain ⟨rightInverse, areaIdentity, tube, _⟩ := coordinates ((trajectory.curve time).2.2 index)
    (nearby.trans_le (min_le_left _ _))
  have physicalRightInverse : diskPhysicalSpectralChart (trajectory.spectralCoordinate index time) =
      (trajectory.curve time).2.2 index := rightInverse
  have area : diskSpectralTubularArea (trajectory.spectralCoordinate index time) = Real.pi :=
    areaIdentity.trans (trajectory.shape_area_eq_pi_of_margin initialCircles marginPositive inside beforeFinal safe index)
  have equation := equations trajectory initialCircles marginPositive time interior (safe time inside) index
    (nearby.trans_le (min_le_right _ _))
  have neutralDerivative := diskSpectralScaledNeutral_trajectory_hasDerivAt (configuration.density index) equation
  have smallEight : 8 * (trajectory.movingFamily.patch index).radius ≤ distance := by
    linarith [(trajectory.movingFamily.patch index).radius_positive]
  have forcingIdentity := trajectory.spectralForcing_eq_canonical_of_margin initialClock marginPositive
    interior inside safe index positive smallEight separated physicalRightInverse
  have estimate := speedBound trajectory.movingFamily index time distance weight (configuration.density index)
    positive weightNonnegative small separated weightBound (Circle.exp (configuration.density index * time / 2))
    (trajectory.spectralCoordinate index time) tube.le area
  rw [← forcingIdentity] at estimate
  exact ⟨_, neutralDerivative, estimate⟩

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
