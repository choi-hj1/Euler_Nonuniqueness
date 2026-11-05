import EulerNonuniqueness.Section3.MovingCentroidGaugeNeutralVelocity
import EulerNonuniqueness.Section3.DiskAngularNeutralProjection

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance movingGaugeAngularVelocityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

theorem exists_uniform_spectral_angular_velocity_radius :
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
        HasDerivAt (fun current => diskNeutralCLM (trajectory.spectralCoordinate index current)) velocity time ∧
        ‖velocity‖ ≤ constant *
          (|configuration.density index| * ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖ ^ 2 +
            weight * ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖) := by
  obtain ⟨radius, positiveRadius, neutralConstant, neutralOne, bounds⟩ :=
    exists_uniform_spectral_neutral_velocity_radius
  let constant := (‖diskNeutralCLM‖ + 1) * neutralConstant
  have constantOne : 1 ≤ constant := by
    have nonnegative := norm_nonneg diskNeutralCLM
    dsimp only [constant]
    nlinarith
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory initialCircles initialClock marginPositive horizon time distance weight inside beforeFinal safe
    index positive weightNonnegative small separated weightBound nearby
  obtain ⟨velocity, derivative, estimate⟩ := bounds trajectory initialCircles initialClock marginPositive
    horizon time distance weight inside beforeFinal safe index positive weightNonnegative small separated weightBound nearby
  refine ⟨diskNeutralCLM velocity, diskNeutralCLM_hasDerivAt_of_relabelNeutral derivative, ?_⟩
  have actual := (diskNeutralCLM.le_opNorm velocity).trans
    (mul_le_mul_of_nonneg_left estimate (norm_nonneg diskNeutralCLM))
  have coefficient : ‖diskNeutralCLM‖ * neutralConstant ≤ constant := by
    rw [show constant = (‖diskNeutralCLM‖ + 1) * neutralConstant from rfl]
    nlinarith
  generalize pointEq : trajectory.spectralCoordinate index time = point at actual ⊢
  have budgetNonnegative : 0 ≤ |configuration.density index| * ‖diskPhysicalTransverseProjection point‖ ^ 2 +
      weight * ‖diskPhysicalTransverseProjection point‖ := by positivity
  exact actual.trans (by nlinarith [mul_le_mul_of_nonneg_right coefficient budgetNonnegative])

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
