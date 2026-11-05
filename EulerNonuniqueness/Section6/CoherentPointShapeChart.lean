import EulerNonuniqueness.Section6.FullPointShapeDynamics

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem unwrappedShapeArgument_leftHalfPlane {point : ℂ} (left : point.re < 0) :
    unwrappedShapeArgument point = Real.pi + (Complex.log (-point)).im := by
  simp only [Complex.log_im]
  unfold unwrappedShapeArgument
  by_cases negative : point.arg < 0
  · rw [if_pos negative, Complex.arg_neg_eq_arg_add_pi_of_im_neg (Complex.arg_neg_iff.mp negative)]
    ring
  · have imaginaryNonnegative : 0 ≤ point.im := by
      exact le_of_not_gt (fun smaller => negative (Complex.arg_neg_iff.mpr smaller))
    have phaseIdentity : (-point).arg = point.arg - Real.pi := by
      apply Complex.arg_neg_eq_arg_sub_pi_iff.mpr
      rcases lt_or_eq_of_le imaginaryNonnegative with positive | zero
      · exact Or.inl positive
      · exact Or.inr ⟨zero.symm, left⟩
    rw [if_neg negative, phaseIdentity]
    ring

theorem unwrappedShapeArgument_hasDerivAt {field : ℝ → ℂ} {velocity : ℂ} {time : ℝ}
    (derivative : HasDerivAt field velocity time) (left : (field time).re < 0) :
    HasDerivAt (fun current => unwrappedShapeArgument (field current)) (velocity / field time).im time := by
  have slit : -(field time) ∈ Complex.slitPlane := Or.inl (by simpa only [Complex.neg_re] using neg_pos.mpr left)
  have logarithm := derivative.neg.clog_real slit
  have imaginary := Complex.imCLM.hasFDerivAt.comp_hasDerivAt time logarithm
  have phase := imaginary.const_add Real.pi
  have phaseDerivative : HasDerivAt (fun current => Real.pi + (Complex.log (-(field current))).im)
      (velocity / field time).im time := by
    simpa only [Complex.imCLM_apply, neg_div_neg_eq] using phase
  apply phaseDerivative.congr_of_eventuallyEq
  have eventuallyLeft : ∀ᶠ current in 𝓝 time, (field current).re < 0 :=
    (Complex.continuous_re.continuousAt.comp derivative.continuousAt).eventually_lt continuousAt_const left
  exact eventuallyLeft.mono fun current currentLeft => unwrappedShapeArgument_leftHalfPlane currentLeft

theorem unwrappedShapeArgument_hasDerivAt_of_localPhase {field : ℝ → ℂ} {velocity time : ℝ}
    (differentiable : DifferentiableAt ℝ field time)
    (derivative : HasDerivAt (localComplexPhase (field time) field) velocity time)
    (left : (field time).re < 0) :
    HasDerivAt (fun current => unwrappedShapeArgument (field current)) velocity time := by
  have nonzero : field time ≠ 0 := by
    intro zero
    simp only [zero, Complex.zero_re, lt_self_iff_false] at left
  have normalized := localComplexPhase_hasDerivAt differentiable.hasDerivAt nonzero
  have actual := unwrappedShapeArgument_hasDerivAt differentiable.hasDerivAt left
  have identity := derivative.unique normalized
  rw [← identity] at actual
  exact actual

theorem pointShapeChart_forced_equation (coefficient : ℝ) {positive negative : ℝ → ℂ}
    {positiveForcing negativeForcing : ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0)
    (squaresNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ‖negative time‖ < ‖positive time‖)
    (left : (((negative time / positive time) ^ 2) : ℂ).re < 0)
    (positiveDerivative : HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time) + positiveForcing) time)
    (negativeDerivative : HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time) + negativeForcing) time) :
    HasDerivAt (fun current => pointShapeChart (positive current) (negative current))
      (shapeChartVelocity (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
          (pointShapeChart (positive time) (negative time)) +
        pointShapeForcing (positive time) (negative time) positiveForcing negativeForcing) time := by
  have raw := four_point_forced_shape_derivatives coefficient positiveNonzero negativeNonzero
    squaresNonzero normOrder positiveDerivative negativeDerivative
  dsimp only at raw
  have quotient := negativeDerivative.differentiableAt.div positiveDerivative.differentiableAt positiveNonzero
  have quotientDifferentiable : DifferentiableAt ℝ (fun current => (negative current / positive current) ^ 2) time := by
    simpa only [pow_two] using quotient.mul quotient
  have angleDerivative := unwrappedShapeArgument_hasDerivAt_of_localPhase quotientDifferentiable raw.2.1 left
  have periodic := shape_velocities_unwrapped_argument
    (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
    (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2) ((negative time / positive time) ^ 2)
  have radial := raw.1
  rw [← periodic.1] at radial
  rw [← periodic.2.1] at angleDerivative
  have chart := shapeChart_forced_hasDerivAt
    (ratio := fun current => ‖negative current‖ ^ 2 / ‖positive current‖ ^ 2)
    (angle := fun current => unwrappedShapeArgument ((negative current / positive current) ^ 2))
    (frequency := coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
    (radialForcing := 2 * (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2) *
      (negativeForcing / negative time - positiveForcing / positive time).re)
    (angularForcing := 2 * (negativeForcing / negative time - positiveForcing / positive time).im)
    radial angleDerivative
  simpa only [pointShapeChart, pointShapeForcing, pointShapeRatio, pointShapeAngle] using chart

end EulerNonuniqueness.Section6
