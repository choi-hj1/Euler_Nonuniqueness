import EulerNonuniqueness.General.LinearEquivariantJets

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem HasFDerivAt.linear_conjugate {source target : Space → Space}
    {derivative : Space →L[ℝ] Space} {base : Space}
    (regular : HasFDerivAt source derivative base) (relabel : Space ≃L[ℝ] Space)
    (equivariant : (fun point => target (relabel point)) =ᶠ[𝓝 base]
      (fun point => relabel (source point))) :
    HasFDerivAt target
      (relabel.toContinuousLinearMap.comp (derivative.comp relabel.symm.toContinuousLinearMap))
      (relabel base) := by
  have inverseRegular : HasFDerivAt source derivative (relabel.symm (relabel base)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using regular
  have composed := relabel.toContinuousLinearMap.hasFDerivAt.comp (relabel base)
    (inverseRegular.comp (relabel base) relabel.symm.toContinuousLinearMap.hasFDerivAt)
  have inverseContinuous : Tendsto relabel.symm (𝓝 (relabel base)) (𝓝 base) := by
    have continuous : ContinuousAt relabel.symm (relabel base) := relabel.symm.continuous.continuousAt
    change Tendsto relabel.symm (𝓝 (relabel base)) (𝓝 (relabel.symm (relabel base))) at continuous
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using continuous
  have equality : target =ᶠ[𝓝 (relabel base)]
      (fun point => relabel (source (relabel.symm point))) := by
    filter_upwards [inverseContinuous.eventually equivariant] with point identity
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using identity
  exact composed.congr_of_eventuallyEq equality

theorem linear_conjugate_derivative_norm_le {source target : Space → Space}
    {derivative : Space →L[ℝ] Space} {base : Space}
    (regular : HasFDerivAt source derivative base) (relabel : Space ≃L[ℝ] Space)
    (equivariant : (fun point => target (relabel point)) =ᶠ[𝓝 base]
      (fun point => relabel (source point))) :
    ‖fderiv ℝ target (relabel base)‖ ≤
      ‖relabel.toContinuousLinearMap‖ * ‖derivative‖ * ‖relabel.symm.toContinuousLinearMap‖ := by
  rw [(HasFDerivAt.linear_conjugate regular relabel equivariant).fderiv]
  have inner := ContinuousLinearMap.opNorm_comp_le derivative relabel.symm.toContinuousLinearMap
  calc
    _ ≤ ‖relabel.toContinuousLinearMap‖ *
        ‖derivative.comp relabel.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖relabel.toContinuousLinearMap‖ *
        (‖derivative‖ * ‖relabel.symm.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left inner (norm_nonneg _)
    _ = _ := by ring

end EulerNonuniqueness.General
