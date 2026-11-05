import EulerNonuniqueness.General.ChartedRealForcingResidual
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def affineForcingCorrection (base value : Space) (linear : Space →L[ℝ] Space) (point : Space) : Space :=
  value + linear (point - base)

theorem affineForcingCorrection_base (base value : Space) (linear : Space →L[ℝ] Space) :
    affineForcingCorrection base value linear base = value := by
  simp only [affineForcingCorrection, sub_self, map_zero, add_zero]

theorem affineForcingCorrection_hasFDerivAt (base value : Space) (linear : Space →L[ℝ] Space) (point : Space) :
    HasFDerivAt (affineForcingCorrection base value linear) linear point := by
  have outer : HasFDerivAt linear linear (point - base) := linear.hasFDerivAt
  have shifted : HasFDerivAt (fun current : Space => current - base) (ContinuousLinearMap.id ℝ Space) point :=
    (hasFDerivAt_id point).sub_const base
  have result := (outer.comp point shifted).const_add value
  simpa only [affineForcingCorrection, ContinuousLinearMap.comp_id] using result

theorem affineForcingCorrection_fderiv (base value : Space) (linear : Space →L[ℝ] Space) (point : Space) :
    fderiv ℝ (affineForcingCorrection base value linear) point = linear :=
  (affineForcingCorrection_hasFDerivAt base value linear point).fderiv

theorem realForcingResidual_affine_hasFDerivAt (field forcing : Space → Space) (base value partnerValue : Space)
    (generator forcingDerivative linear partnerLinear : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (frequency : ℝ)
    (fieldJet : HasFDerivAt field generator base)
    (fieldSecondJet : HasFDerivAt (fderiv ℝ field) second base)
    (forcingJet : HasFDerivAt forcing forcingDerivative base) :
    HasFDerivAt
      (realForcingResidual field forcing (affineForcingCorrection base value linear)
        (affineForcingCorrection base partnerValue partnerLinear) frequency)
      (forcingDerivative + (generator.comp linear + second.flip value) - linear.comp generator - frequency • partnerLinear) base := by
  have correctionJet := affineForcingCorrection_hasFDerivAt base value linear base
  have applied := fieldSecondJet.clm_apply correctionJet
  rw [fieldJet.fderiv, affineForcingCorrection_base] at applied
  have linearJet : HasFDerivAt linear linear (field base) := linear.hasFDerivAt
  have paired := linearJet.comp base fieldJet
  have partnerJet := affineForcingCorrection_hasFDerivAt base partnerValue partnerLinear base
  have result := ((forcingJet.add applied).sub paired).sub (partnerJet.const_smul frequency)
  unfold realForcingResidual
  simpa only [affineForcingCorrection_fderiv, Function.comp_apply] using result

theorem realForcingResidual_affine_value (field forcing : Space → Space) (base value partnerValue : Space)
    (generator linear partnerLinear : Space →L[ℝ] Space) (frequency : ℝ)
    (fieldJet : HasFDerivAt field generator base) (stationary : field base = 0) :
    realForcingResidual field forcing (affineForcingCorrection base value linear)
        (affineForcingCorrection base partnerValue partnerLinear) frequency base =
      forcing base + generator value - frequency • partnerValue := by
  simp only [realForcingResidual, affineForcingCorrection_base, affineForcingCorrection_fderiv,
    fieldJet.fderiv, stationary, map_zero, sub_zero]

theorem realForcingResidual_affine_fderiv (field forcing : Space → Space) (base value partnerValue : Space)
    (generator forcingDerivative linear partnerLinear : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (frequency : ℝ)
    (fieldJet : HasFDerivAt field generator base)
    (fieldSecondJet : HasFDerivAt (fderiv ℝ field) second base)
    (forcingJet : HasFDerivAt forcing forcingDerivative base) :
    fderiv ℝ
      (realForcingResidual field forcing (affineForcingCorrection base value linear)
        (affineForcingCorrection base partnerValue partnerLinear) frequency) base =
      forcingDerivative + second.flip value + generator.comp linear - linear.comp generator - frequency • partnerLinear := by
  rw [(realForcingResidual_affine_hasFDerivAt field forcing base value partnerValue generator forcingDerivative
    linear partnerLinear second frequency fieldJet fieldSecondJet forcingJet).fderiv]
  abel

end EulerNonuniqueness.General
