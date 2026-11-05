import EulerNonuniqueness.General.PlaneVariationalArea

noncomputable section

open Set
open scoped Topology

namespace Complex

theorem linearMap_det_eq_orientedArea (linear : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det linear = orientedArea (linear 1) (linear I) := by
  rw [← LinearMap.det_toMatrix basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, coe_basisOneI_repr, coe_basisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, orientedArea]
  ring

theorem det_eq_one_of_variational_trace_zero
    {coefficient jacobian : ℝ → ℂ →L[ℝ] ℂ} {start finish : ℝ}
    (initial : jacobian start = ContinuousLinearMap.id ℝ ℂ)
    (continuous : ContinuousOn jacobian (Icc start finish))
    (equation : ∀ direction time, time ∈ Ico start finish →
      HasDerivWithinAt (fun nextTime => jacobian nextTime direction)
        (coefficient time (jacobian time direction)) (Ici time) time)
    (traceZero : ∀ time ∈ Ico start finish, (coefficient time 1).re + (coefficient time I).im = 0) :
    ∀ time ∈ Icc start finish, LinearMap.det (jacobian time).toLinearMap = 1 := by
  have area := orientedArea_constant_of_trace_zero
    (continuous.clm_apply continuousOn_const) (continuous.clm_apply continuousOn_const)
    (equation 1) (equation I) traceZero
  intro time inside
  rw [linearMap_det_eq_orientedArea]
  change orientedArea (jacobian time 1) (jacobian time I) = 1
  rw [area time inside, initial]
  simp [orientedArea]

end Complex
