import EulerNonuniqueness.Section3.MovingCentroidGaugeAngularVelocity

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] movingGaugeAngularVelocityC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

open EulerNonuniqueness.Section6

theorem exists_uniform_spectral_angular_cost_radius :
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
      ∀ (index : Fin count) (positive : 0 < distance), 0 ≤ weight → configuration.density index ≠ 0 →
      192 * (trajectory.movingFamily.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
        distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time)
        ((trajectory.movingFamily.patch index).center time) position) ≤ weight →
      ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
      ∃ velocity : PeriodicC1HolderHalf,
        HasDerivAt (fun current => diskNeutralCLM (trajectory.spectralCoordinate index current)) velocity time ∧
        (weight / |configuration.density index|) * ‖velocity‖ ≤ constant *
          (weight * ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖ ^ 2 +
            (weight ^ 2 / |configuration.density index|) *
              ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖) := by
  obtain ⟨radius, positiveRadius, constant, constantOne, bounds⟩ :=
    exists_uniform_spectral_angular_velocity_radius
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    initialCircles initialClock marginPositive horizon time distance weight inside beforeFinal safe index positive
    weightNonnegative nonzero small separated weightBound nearby
  obtain ⟨velocity, derivative, estimate⟩ := bounds trajectory initialCircles initialClock marginPositive
    horizon time distance weight inside beforeFinal safe index positive weightNonnegative small separated weightBound nearby
  refine ⟨velocity, derivative, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left estimate
    (div_nonneg weightNonnegative (abs_nonneg (configuration.density index)))
  generalize pointEq : diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time) = point at scaled ⊢
  have scalarIdentity (modulus : ℝ) (modulusPositive : 0 < modulus) :
      (weight / modulus) * (constant * (modulus * ‖point‖ ^ 2 + weight * ‖point‖)) =
        constant * (weight * ‖point‖ ^ 2 + (weight ^ 2 / modulus) * ‖point‖) := by
    field_simp [modulusPositive.ne']
    <;> ring
  exact scaled.trans_eq (scalarIdentity |configuration.density index| (abs_pos.mpr nonzero))

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
