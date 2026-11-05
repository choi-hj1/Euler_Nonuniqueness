import EulerNonuniqueness.Section3.PointContourReparametrization
import EulerNonuniqueness.Section3.FixedRelabelEquivalence
import EulerNonuniqueness.Section3.ContourLocalEvolution

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem PeriodicC1LabelMap.contourVelocity_compose (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    contourVelocity (labels.compose data).val.1 (labels.compose data).val.2.val.1 target (-Real.pi) Real.pi =
      contourVelocity data.val.1 data.val.2.val.1 (labels.map target) (-Real.pi) Real.pi := by
  calc
    _ = pointContourVelocity (labels.compose data).val.1 (labels.compose data).val.2.val.1
        ((labels.compose data).val.1 target) (-Real.pi) Real.pi :=
      (pointContourVelocity_on_curve _ _ target (-Real.pi) Real.pi).symm
    _ = pointContourVelocity data.val.1 data.val.2.val.1 (data.val.1 (labels.map target)) (-Real.pi) Real.pi := by
      rw [labels.compose_value]
      exact (labels.pointContourVelocity_compose positive data small _).2
    _ = _ := pointContourVelocity_on_curve _ _ (labels.map target) (-Real.pi) Real.pi

theorem PeriodicC1LabelMap.contourVelocityBanach_compose (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖labels.compose data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBanach (labels.compose data) composedSmall = labels.compose (contourVelocityBanach data small) := by
  apply PeriodicC1HolderHalf.ext_value
  intro target
  rw [contourVelocityBanach_value, labels.compose_value, contourVelocityBanach_value]
  exact labels.contourVelocity_compose positive data (small.trans_le (min_le_right _ _)) target

theorem PeriodicC1LabelMap.extendedContourVelocity_compose (labels : PeriodicC1LabelMap)
    (positive : ∀ label, 0 < labels.slope label) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖labels.compose data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (labels.compose data) = labels.compose (extendedContourVelocity data) := by
  rw [extendedContourVelocity_eq _ composedSmall, extendedContourVelocity_eq _ small]
  exact labels.contourVelocityBanach_compose positive data small composedSmall

theorem extendedContourVelocity_fixedRelabelEquivalence (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (fixedRelabelEquivalence angular angularSmall data) =
      fixedRelabelEquivalence angular angularSmall (extendedContourVelocity data) := by
  have positive (label : ℝ) : 0 < (periodicForwardLabelMap angular angularSmall).slope label := by
    change 0 < periodicLabelSlope angular label
    exact (by linarith : 0 < 1 - ‖angular‖).trans_le (periodicLabelSlope_lower angular label)
  exact (periodicForwardLabelMap angular angularSmall).extendedContourVelocity_compose positive data small composedSmall

end EulerNonuniqueness.Paper
