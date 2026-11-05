import EulerNonuniqueness.General.LinearODEExistence
import EulerNonuniqueness.General.PlaneJacobian

noncomputable section

open Set
open scoped NNReal Topology

namespace EulerNonuniqueness

def planeLinearMapFromColumns (first second : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight first + Complex.imCLM.smulRight second

theorem exists_plane_variational_on_Icc {coefficient : ℝ → ℂ →L[ℝ] ℂ}
    {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (continuous : ContinuousOn coefficient (Icc 0 horizon)) {bound : ℝ≥0}
    (bounded : ∀ time ∈ Icc 0 horizon, ‖coefficient time‖ ≤ bound) :
    ∃ jacobian : ℝ → ℂ →L[ℝ] ℂ,
      jacobian 0 = ContinuousLinearMap.id ℝ ℂ ∧ ContinuousOn jacobian (Icc 0 horizon) ∧
      ∀ direction time, time ∈ Icc 0 horizon →
        HasDerivWithinAt (fun next => jacobian next direction)
          (coefficient time (jacobian time direction)) (Icc 0 horizon) time := by
  obtain ⟨first, firstInitial, firstContinuous, firstDerivative, _⟩ :=
    exists_linearODE_on_Icc nonnegative continuous bounded (1 : ℂ)
  obtain ⟨second, secondInitial, secondContinuous, secondDerivative, _⟩ :=
    exists_linearODE_on_Icc nonnegative continuous bounded Complex.I
  let jacobian := fun time => planeLinearMapFromColumns (first time) (second time)
  refine ⟨jacobian, ?_, ?_, ?_⟩
  · ext direction
    simp only [jacobian, planeLinearMapFromColumns, firstInitial, secondInitial,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, ContinuousLinearMap.id_apply]
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im direction
  · exact (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ) Complex.reCLM).continuous.comp_continuousOn firstContinuous).add
      (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ) Complex.imCLM).continuous.comp_continuousOn secondContinuous)
  · intro direction time inside
    have derivative := ((firstDerivative time inside).const_smul direction.re).add
      ((secondDerivative time inside).const_smul direction.im)
    simpa only [jacobian, planeLinearMapFromColumns, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      map_add, map_smul] using derivative

end EulerNonuniqueness
