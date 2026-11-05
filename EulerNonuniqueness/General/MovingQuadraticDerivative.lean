import EulerNonuniqueness.General.QuadraticHomologicalLinearMap

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Parameter : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

theorem moving_quadratic_diagonal_hasDerivAt
    {coefficient : Parameter → BilinearEnd Space} {parameter : ℝ → Parameter}
    {trajectory : ℝ → Space} {time : ℝ} {parameterVelocity : Parameter} {velocity : Space}
    {coefficientDerivative : Parameter →L[ℝ] BilinearEnd Space}
    (coefficientDifferentiable : HasFDerivAt coefficient coefficientDerivative (parameter time))
    (parameterEquation : HasDerivAt parameter parameterVelocity time)
    (trajectoryEquation : HasDerivAt trajectory velocity time) :
    HasDerivAt (fun current => coefficient (parameter current) (trajectory current) (trajectory current))
      (coefficientDerivative parameterVelocity (trajectory time) (trajectory time) +
        coefficient (parameter time) velocity (trajectory time) +
        coefficient (parameter time) (trajectory time) velocity) time := by
  have differentiated : HasDerivAt (fun current => coefficient (parameter current))
      (coefficientDerivative parameterVelocity) time :=
    HasFDerivAt.comp_hasDerivAt (F := Parameter) (E := BilinearEnd Space) time
      coefficientDifferentiable parameterEquation
  convert (differentiated.clm_apply trajectoryEquation).clm_apply trajectoryEquation using 1 <;>
    simp only [ContinuousLinearMap.add_apply, add_assoc]

theorem moving_quadratic_coordinate_hasDerivAt
    {coefficient : Parameter → BilinearEnd Space} {parameter : ℝ → Parameter}
    {trajectory : ℝ → Space} {time : ℝ} {parameterVelocity : Parameter} {velocity : Space}
    {coefficientDerivative : Parameter →L[ℝ] BilinearEnd Space}
    (coefficientDifferentiable : HasFDerivAt coefficient coefficientDerivative (parameter time))
    (parameterEquation : HasDerivAt parameter parameterVelocity time)
    (trajectoryEquation : HasDerivAt trajectory velocity time) :
    HasDerivAt (fun current => trajectory current -
        coefficient (parameter current) (trajectory current) (trajectory current))
      (velocity - (coefficientDerivative parameterVelocity (trajectory time) (trajectory time) +
        coefficient (parameter time) velocity (trajectory time) +
        coefficient (parameter time) (trajectory time) velocity)) time :=
  trajectoryEquation.sub (moving_quadratic_diagonal_hasDerivAt coefficientDifferentiable
    parameterEquation trajectoryEquation)

theorem moving_quadratic_coordinate_hasDerivAt_of_frozen
    {coefficient : Parameter → BilinearEnd Space} {parameter : ℝ → Parameter}
    {trajectory : ℝ → Space} {time : ℝ} {parameterVelocity : Parameter}
    {velocity frozenVelocity : Space}
    {coefficientDerivative : Parameter →L[ℝ] BilinearEnd Space}
    (coefficientDifferentiable : HasFDerivAt coefficient coefficientDerivative (parameter time))
    (parameterEquation : HasDerivAt parameter parameterVelocity time)
    (trajectoryEquation : HasDerivAt trajectory velocity time)
    (frozenEquation : HasDerivAt (fun current => trajectory current -
        coefficient (parameter time) (trajectory current) (trajectory current)) frozenVelocity time) :
    HasDerivAt (fun current => trajectory current -
        coefficient (parameter current) (trajectory current) (trajectory current))
      (frozenVelocity - coefficientDerivative parameterVelocity (trajectory time) (trajectory time)) time := by
  have frozenActual := trajectoryEquation.sub
    (((hasDerivAt_const time (coefficient (parameter time))).clm_apply trajectoryEquation).clm_apply
      trajectoryEquation)
  have identity := frozenEquation.unique frozenActual
  have moving := moving_quadratic_coordinate_hasDerivAt coefficientDifferentiable
    parameterEquation trajectoryEquation
  convert moving using 1
  rw [identity]
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  abel

end

end EulerNonuniqueness.General
