import EulerNonuniqueness.General.ChartedRealForcingResidual
import EulerNonuniqueness.General.ContinuousCoefficientJet

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem realForcingResidual_stationary_hasFDerivAt
    (field forcing correction partner : Space → Space) (base : Space)
    (generator forcingDerivative correctionDerivative partnerDerivative : Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (frequency : ℝ)
    (fieldJet : HasFDerivAt field generator base)
    (fieldSecondJet : HasFDerivAt (fderiv ℝ field) second base)
    (forcingJet : HasFDerivAt forcing forcingDerivative base)
    (correctionJet : HasFDerivAt correction correctionDerivative base)
    (correctionContinuous : ContinuousAt (fderiv ℝ correction) base)
    (partnerJet : HasFDerivAt partner partnerDerivative base)
    (stationary : field base = 0) :
    HasFDerivAt (realForcingResidual field forcing correction partner frequency)
      (forcingDerivative + (generator.comp correctionDerivative + second.flip (correction base)) -
        correctionDerivative.comp generator - frequency • partnerDerivative) base := by
  have applied := fieldSecondJet.clm_apply correctionJet
  rw [fieldJet.fderiv] at applied
  have paired := continuous_coefficient_vanishing_factor_hasFDerivAt
    (fderiv ℝ correction) field base generator correctionContinuous fieldJet stationary
  rw [correctionJet.fderiv] at paired
  exact ((forcingJet.add applied).sub paired).sub (partnerJet.const_smul frequency)

theorem realForcingResidual_stationary_value
    (field forcing correction partner : Space → Space) (base : Space)
    (generator : Space →L[ℝ] Space) (frequency : ℝ)
    (fieldJet : HasFDerivAt field generator base) (stationary : field base = 0) :
    realForcingResidual field forcing correction partner frequency base =
      forcing base + generator (correction base) - frequency • partner base := by
  simp only [realForcingResidual, fieldJet.fderiv, stationary, map_zero, sub_zero]

end EulerNonuniqueness.General
