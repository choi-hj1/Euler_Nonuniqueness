import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialData

noncomputable section

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem movingPatch_boundary_initial_circle
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (index : Fin count) (label : ℝ) :
    (trajectory.movingPatch index).boundary 0 label = initial.2.1 index +
      (configuration.radius index : ℂ) * Complex.exp (Complex.I * (label : ℂ)) := by
  rw [MovingMaterialPatch.boundary, trajectory.movingPatch_phase_initial initialClock,
    trajectory.movingPatch_shape_initial, initialCircles]
  change trajectory.center index 0 + configuration.radius index •
    ((Circle.exp 0 : ℂ) * standardCircleBanach.val.1 label) = _
  rw [trajectory.center_initial]
  simp only [Circle.exp_zero, Circle.coe_one, one_mul, Complex.real_smul]
  change initial.2.1 index + (configuration.radius index : ℂ) * Complex.exp ((label : ℂ) * Complex.I) = _
  rw [mul_comm (label : ℂ) Complex.I]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
