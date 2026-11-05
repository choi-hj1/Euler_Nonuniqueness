import EulerNonuniqueness.Section3.RotatingForcingRelabelResidual

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance fixedCorrectionBoundsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem fixedRelabelEquivalence_operator_norm_le (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) :
    ‖(fixedRelabelEquivalence angular small).toContinuousLinearMap‖ ≤ 8 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fixedRelabelEquivalence_norm_bound angular small)

theorem fixedRelabelEquivalence_inverse_operator_norm_le (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2) :
    ‖(fixedRelabelEquivalence angular small).symm.toContinuousLinearMap‖ ≤ 12 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fixedRelabelEquivalence_symm_norm_bound angular small)

theorem fixedRelabelCorrection_value_norm_le (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (correction : PeriodicC1HolderHalf → PeriodicC1HolderHalf) (data : PeriodicC1HolderHalf) :
    ‖EulerNonuniqueness.General.linearRelabelCorrection (fixedRelabelEquivalence angular small) correction
      (fixedRelabelEquivalence angular small data)‖ ≤ 8 * ‖correction data‖ := by
  simp only [EulerNonuniqueness.General.linearRelabelCorrection, ContinuousLinearEquiv.symm_apply_apply]
  exact fixedRelabelEquivalence_norm_bound angular small (correction data)

theorem fixedRelabelCorrection_derivative_norm_le (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (correction : PeriodicC1HolderHalf → PeriodicC1HolderHalf) (data : PeriodicC1HolderHalf)
    (regular : DifferentiableAt ℝ correction data) :
    ‖fderiv ℝ (EulerNonuniqueness.General.linearRelabelCorrection (fixedRelabelEquivalence angular small) correction)
      (fixedRelabelEquivalence angular small data)‖ ≤ 96 * ‖fderiv ℝ correction data‖ := by
  let relabel := fixedRelabelEquivalence angular small
  have intertwines := EulerNonuniqueness.General.linearRelabelCorrection_fderiv relabel correction data regular
  have identity : fderiv ℝ (EulerNonuniqueness.General.linearRelabelCorrection relabel correction) (relabel data) =
      relabel.toContinuousLinearMap.comp ((fderiv ℝ correction data).comp relabel.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro direction
    have evaluated := congrArg (fun derivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
      derivative (relabel.symm direction)) intertwines
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using evaluated
  rw [identity]
  have estimate := ContinuousLinearMap.opNorm_comp_le relabel.toContinuousLinearMap
    ((fderiv ℝ correction data).comp relabel.symm.toContinuousLinearMap)
  have inner := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ correction data) relabel.symm.toContinuousLinearMap
  have first := fixedRelabelEquivalence_operator_norm_le angular small
  have second := fixedRelabelEquivalence_inverse_operator_norm_le angular small
  calc
    _ ≤ ‖relabel.toContinuousLinearMap‖ *
        (‖fderiv ℝ correction data‖ * ‖relabel.symm.toContinuousLinearMap‖) :=
      estimate.trans (mul_le_mul_of_nonneg_left inner (norm_nonneg _))
    _ ≤ 8 * (‖fderiv ℝ correction data‖ * 12) :=
      mul_le_mul first (mul_le_mul_of_nonneg_left second (norm_nonneg _)) (by positivity) (by norm_num)
    _ = _ := by ring

end EulerNonuniqueness.Paper
