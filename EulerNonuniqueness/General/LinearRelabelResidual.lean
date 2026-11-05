import EulerNonuniqueness.General.LinearEquivariantJets

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def linearRelabelCorrection (relabel : Space ≃L[ℝ] Space) (correction : Space → Space) : Space → Space :=
  fun point => relabel (correction (relabel.symm point))

def forcingJetResidual (field forcing correction : Space → Space) (weight : Space →L[ℝ] Space) (point : Space) : Space :=
  forcing point + fderiv ℝ field point (correction point) -
    fderiv ℝ correction point (field point) - weight (correction point)

theorem linearRelabelCorrection_fderiv (relabel : Space ≃L[ℝ] Space) (correction : Space → Space)
    (base : Space) (regular : DifferentiableAt ℝ correction base) :
    (fderiv ℝ (linearRelabelCorrection relabel correction) (relabel base)).comp relabel.toContinuousLinearMap =
      relabel.toContinuousLinearMap.comp (fderiv ℝ correction base) := by
  have inner : HasFDerivAt correction (fderiv ℝ correction base) (relabel.symm (relabel base)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using regular.hasFDerivAt
  have derivative := relabel.toContinuousLinearMap.hasFDerivAt.comp (relabel base)
    (inner.comp (relabel base) relabel.symm.toContinuousLinearMap.hasFDerivAt)
  change HasFDerivAt (linearRelabelCorrection relabel correction) _ _ at derivative
  have identity := derivative.fderiv
  rw [identity]
  ext direction
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem forcingJetResidual_linearRelabel (field forcing correction : Space → Space)
    (weight : Space →L[ℝ] Space) (relabel : Space ≃L[ℝ] Space) (base : Space)
    (fieldRegular : DifferentiableAt ℝ field base) (imageRegular : DifferentiableAt ℝ field (relabel base))
    (correctionRegular : DifferentiableAt ℝ correction base)
    (fieldEquivariant : (fun point => field (relabel point)) =ᶠ[𝓝 base] (fun point => relabel (field point)))
    (forcingEquivariant : forcing (relabel base) = relabel (forcing base))
    (weightCommutes : ∀ direction, weight (relabel direction) = relabel (weight direction)) :
    forcingJetResidual field forcing (linearRelabelCorrection relabel correction) weight (relabel base) =
      relabel (forcingJetResidual field forcing correction weight base) := by
  have fieldDerivative := fderiv_linear_equivariant field relabel.toContinuousLinearMap base
    fieldRegular imageRegular fieldEquivariant
  have correctionDerivative := linearRelabelCorrection_fderiv relabel correction base correctionRegular
  have fieldValue : field (relabel base) = relabel (field base) := fieldEquivariant.self_of_nhds
  unfold forcingJetResidual
  have correctionValue : linearRelabelCorrection relabel correction (relabel base) = relabel (correction base) := by
    simp only [linearRelabelCorrection, ContinuousLinearEquiv.symm_apply_apply]
  rw [correctionValue, forcingEquivariant, fieldValue, weightCommutes]
  have first := congrArg (fun derivative : Space →L[ℝ] Space => derivative (correction base)) fieldDerivative
  have second := congrArg (fun derivative : Space →L[ℝ] Space => derivative (field base)) correctionDerivative
  change fderiv ℝ field (relabel base) (relabel (correction base)) = relabel (fderiv ℝ field base (correction base)) at first
  change fderiv ℝ (linearRelabelCorrection relabel correction) (relabel base) (relabel (field base)) =
    relabel (fderiv ℝ correction base (field base)) at second
  rw [first, second, map_sub, map_sub, map_add]

end EulerNonuniqueness.General
