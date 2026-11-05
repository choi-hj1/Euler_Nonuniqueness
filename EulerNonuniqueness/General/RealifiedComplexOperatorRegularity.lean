import EulerNonuniqueness.General.RealifiedComplexOperatorDifference
import EulerNonuniqueness.General.ContinuousSubPreservingRegularity

noncomputable section

namespace EulerNonuniqueness.General

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

theorem realifiedComplexOperator_hasLipschitzDerivativeNear
    (output : ComplexSpace →L[ℝ] RealSpace) (input : RealSpace →L[ℝ] ComplexSpace)
    (coefficient : ℂ) (point : ComplexSpace →L[ℂ] ComplexSpace) :
    HasLipschitzDerivativeNear
      (fun operator : ComplexSpace →L[ℂ] ComplexSpace => realifiedComplexOperator output input operator coefficient)
      point := by
  apply hasLipschitzDerivativeNear_of_sub_preserving
  · intro first second
    exact (realifiedComplexOperator_sub output input first second coefficient).symm
  · have bounded : LipschitzWith
        ⟨‖output‖ * ‖coefficient‖ * ‖input‖, by positivity⟩
        (fun operator : ComplexSpace →L[ℂ] ComplexSpace =>
          realifiedComplexOperator output input operator coefficient) := by
      apply LipschitzWith.of_dist_le_mul
      intro first second
      simp only [dist_eq_norm, NNReal.coe_mk]
      rw [realifiedComplexOperator_sub]
      calc
        _ ≤ ‖output‖ * ‖coefficient‖ * ‖first - second‖ * ‖input‖ :=
          realifiedComplexOperator_norm_le output input (first - second) coefficient
        _ = _ := by ring
    exact bounded.continuous

end EulerNonuniqueness.General
