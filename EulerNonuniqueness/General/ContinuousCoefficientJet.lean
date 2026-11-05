import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space First Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup First] [NormedSpace ℝ First]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem continuous_coefficient_vanishing_factor_hasFDerivAt
    (coefficient : Space → First →L[ℝ] Target) (factor : Space → First)
    (base : Space) (linear : Space →L[ℝ] First)
    (coefficientContinuous : ContinuousAt coefficient base)
    (factorDerivative : HasFDerivAt factor linear base) (factorZero : factor base = 0) :
    HasFDerivAt (fun current => coefficient current (factor current))
      ((coefficient base).comp linear) base := by
  have coefficientZero : Tendsto (fun current => coefficient current - coefficient base)
      (𝓝 base) (𝓝 0) := by
    simpa only [sub_self] using coefficientContinuous.tendsto.sub_const (coefficient base)
  have coefficientSmall : (fun current => coefficient current - coefficient base) =o[𝓝 base]
      (fun _ : Space => (1 : ℝ)) := (isLittleO_one_iff ℝ).2 coefficientZero
  have factorBound : factor =O[𝓝 base] (fun current => current - base) := by
    simpa only [factorZero, sub_zero] using factorDerivative.isBigO_sub
  have scalarSmall : (fun current => ‖coefficient current - coefficient base‖ * ‖factor current‖) =o[𝓝 base]
      (fun current => current - base) := by
    apply Asymptotics.IsLittleO.of_norm_right
    simpa only [one_mul] using coefficientSmall.norm_left.mul_isBigO factorBound.norm_left.norm_right
  have appliedBound : (fun current => (coefficient current - coefficient base) (factor current)) =O[𝓝 base]
      (fun current => ‖coefficient current - coefficient base‖ * ‖factor current‖) :=
    Asymptotics.IsBigO.of_norm_le (fun current => (coefficient current - coefficient base).le_opNorm (factor current))
  have appliedSmall := appliedBound.trans_isLittleO scalarSmall
  have errorDerivative : HasFDerivAt
      (fun current => (coefficient current - coefficient base) (factor current))
      (0 : Space →L[ℝ] Target) base := by
    apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
    have shiftTendsto : Tendsto (fun increment : Space => base + increment) (𝓝 0) (𝓝 base) := by
      have shiftContinuous : Continuous (fun increment : Space => base + increment) :=
        continuous_const.add continuous_id
      simpa only [add_zero] using shiftContinuous.tendsto (0 : Space)
    have shifted := appliedSmall.comp_tendsto shiftTendsto
    simpa only [Function.comp_def, sub_self, ContinuousLinearMap.zero_apply, sub_zero,
      add_sub_cancel_left] using shifted
  have fixedDerivative := (coefficient base).hasFDerivAt.comp base factorDerivative
  have result : HasFDerivAt
      (fun current => coefficient base (factor current) + (coefficient current - coefficient base) (factor current))
      ((coefficient base).comp linear) base := by
    simpa only [add_zero] using fixedDerivative.add errorDerivative
  convert result using 1
  funext current
  rw [ContinuousLinearMap.sub_apply]
  abel

end EulerNonuniqueness.General
