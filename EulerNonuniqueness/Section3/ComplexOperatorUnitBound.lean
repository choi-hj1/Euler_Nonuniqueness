import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

namespace EulerNonuniqueness.General

noncomputable section

variable {Source Target : Type*} [NormedAddCommGroup Source] [NormedAddCommGroup Target]
  [NormedSpace ℂ Source] [NormedSpace ℂ Target]

theorem complex_opNorm_le_of_unit_norm (operator : Source →L[ℂ] Target) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (estimate : ∀ direction, ‖direction‖ = 1 → ‖operator direction‖ ≤ bound) :
    ‖operator‖ ≤ bound := by
  apply ContinuousLinearMap.opNorm_le_bound' operator nonnegative
  intro direction nonzero
  have positive : 0 < ‖direction‖ := (norm_nonneg _).lt_of_ne' nonzero
  have scalarNorm : ‖(‖direction‖ : ℂ)⁻¹‖ = ‖direction‖⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have normalized : ‖(‖direction‖ : ℂ)⁻¹ • direction‖ = 1 := by
    rw [norm_smul, scalarNorm, inv_mul_cancel₀ nonzero]
  have bound := estimate _ normalized
  rw [map_smul, norm_smul, scalarNorm, ← div_eq_inv_mul] at bound
  exact (div_le_iff₀ positive).mp bound

end

end EulerNonuniqueness.General
