import EulerNonuniqueness.Section3.MovingCentroidGaugeNeutralVelocity
import EulerNonuniqueness.General.NormHistoryFromDerivatives

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

local instance movingGaugeNeutralHistoryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

open EulerNonuniqueness.Section6

theorem exists_uniform_spectral_neutral_history_radius :
    ∃ radius > 0, ∃ constant ≥ 1,
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
        ‖diskRelabelNeutralCLM (trajectory.spectralCoordinate index time)‖ ≤
          constant * (|configuration.density index| * transverseRadius ^ 2 + weight * transverseRadius) * time := by
  obtain ⟨radius, radiusPositive, constant, constantOne, bounds⟩ :=
    exists_uniform_spectral_neutral_velocity_radius
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory initialCircles initialClock marginPositive horizon distance weight transverseRadius beforeFinal safe
    index positive weightNonnegative transverseNonnegative small separated weightBound nearby transverseBound
  have actual : ∀ time ∈ Icc 0 horizon, ∃ velocity : PeriodicC1HolderHalf,
      HasDerivAt (fun current => diskRelabelNeutralCLM (trajectory.spectralCoordinate index current)) velocity time ∧
        ‖velocity‖ ≤ constant * (|configuration.density index| * transverseRadius ^ 2 + weight * transverseRadius) := by
    intro time inside
    obtain ⟨velocity, derivative, estimate⟩ := bounds trajectory initialCircles initialClock marginPositive
      horizon time distance weight inside beforeFinal safe index positive weightNonnegative small
      (separated time inside) (weightBound time inside) (nearby time inside)
    refine ⟨velocity, derivative, estimate.trans ?_⟩
    gcongr
    · exact transverseBound time inside
    · exact transverseBound time inside
  have history := EulerNonuniqueness.General.norm_history_le_of_exists_hasDerivAt actual
  have initialZero : diskRelabelNeutralCLM (trajectory.spectralCoordinate index 0) = 0 := by
    rw [trajectory.spectralCoordinate_initial_circle initialCircles, map_zero]
  simpa only [initialZero, sub_zero] using history

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
