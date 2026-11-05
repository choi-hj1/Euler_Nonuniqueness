import EulerNonuniqueness.Section3.ContourContinuousFourierAverage
import EulerNonuniqueness.Section3.ExtendedCrossContour

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

local instance crossContinuousVectorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourLabelShiftCCLM_norm (offset : ℝ) (data : PeriodicC1HolderHalf) :
    ‖contourLabelShiftCCLM offset data‖ = ‖data‖ := by
  change ‖standardCircle offset • normalizedContourShift offset data‖ = _
  rw [norm_smul, standardCircle_norm, one_mul, normalizedContourShift_norm]

theorem extendedCrossContourVelocity_labelShift (target source : PeriodicC1HolderHalf)
    {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ sourceLabel targetLabel, lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖)
    (offset : ℝ) :
    extendedCrossContourVelocity (contourLabelShiftCCLM offset target) source =
      contourLabelShiftCCLM offset (extendedCrossContourVelocity target source) := by
  have shiftedSeparated : ∀ sourceLabel targetLabel,
      lower ≤ ‖(contourLabelShiftCCLM offset target).val.1 targetLabel - source.val.1 sourceLabel‖ := by
    intro sourceLabel targetLabel
    rw [contourLabelShiftCCLM_value]
    exact separated sourceLabel (targetLabel + offset)
  rw [extendedCrossContourVelocity_eq _ _ positive shiftedSeparated]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [crossContourVelocityBanach_value, contourLabelShiftCCLM_value,
    extendedCrossContourVelocity_eq _ _ positive separated, contourLabelShiftCCLM_value,
    crossContourVelocityBanach_value]

theorem continuous_crossContour_label_orbit (target source : PeriodicC1HolderHalf)
    (member : target ∈ contourContinuousVectorSubmodule) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ sourceLabel targetLabel, lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖) :
    Continuous (fun offset => extendedCrossContourVelocity (contourLabelShiftCCLM offset target) source) := by
  let bound := max ‖target‖ ‖source‖
  let admissible : Set PeriodicC1HolderHalf := {data | ‖data‖ ≤ bound ∧
    ∀ sourceLabel targetLabel, lower ≤ ‖data.val.1 targetLabel - source.val.1 sourceLabel‖}
  have boundNonnegative : 0 ≤ bound := (norm_nonneg target).trans (le_max_left _ _)
  have constantNonnegative : 0 ≤ crossContourIntegrandLipschitzBound bound lower / 2 :=
    div_nonneg (crossContourIntegrandLipschitzBound_nonneg boundNonnegative positive) (by norm_num)
  have lipschitz : LipschitzOnWith (Real.toNNReal (crossContourIntegrandLipschitzBound bound lower / 2))
      (fun data => extendedCrossContourVelocity data source) admissible := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro first firstMember second secondMember
    have estimate := extendedCrossContourVelocity_parameter_norm_bound first source second source positive
      firstMember.2 secondMember.2 firstMember.1 (le_max_right _ _) secondMember.1 (le_max_right _ _)
    simpa only [sub_self, norm_zero, add_zero, Real.coe_toNNReal _ constantNonnegative] using estimate
  apply lipschitz.continuousOn.comp_continuous (continuous_contourLabelShiftCCLM target member)
  intro offset
  constructor
  · rw [contourLabelShiftCCLM_norm]
    exact le_max_left _ _
  · intro sourceLabel targetLabel
    rw [contourLabelShiftCCLM_value]
    exact separated sourceLabel (targetLabel + offset)

theorem extendedCrossContourVelocity_mem_contourContinuousVectorSubmodule
    (target source : PeriodicC1HolderHalf) (member : target ∈ contourContinuousVectorSubmodule)
    (separated : UniformlySeparatedContours target source) :
    extendedCrossContourVelocity target source ∈ contourContinuousVectorSubmodule := by
  obtain ⟨lower, positive, gap⟩ := separated
  have pureContinuous : Continuous (fun offset => contourLabelShiftCCLM offset (extendedCrossContourVelocity target source)) := by
    simpa only [extendedCrossContourVelocity_labelShift target source positive gap] using
      continuous_crossContour_label_orbit target source member positive gap
  have circleContinuous : Continuous standardCircle := by unfold standardCircle; fun_prop
  have conjugateContinuous : Continuous (star : ℂ → ℂ) := by fun_prop
  have phaseContinuous : Continuous (fun offset => (standardCircle offset)⁻¹) := by
    simpa only [Function.comp_def, standardCircle_star_eq_inv] using conjugateContinuous.comp circleContinuous
  have normalizedContinuous := phaseContinuous.smul pureContinuous
  change Continuous (fun offset => normalizedContourShiftCLM offset (extendedCrossContourVelocity target source))
  convert normalizedContinuous using 1
  funext offset
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [complexC1Holder_smul_value, contourLabelShiftCCLM_value]
  rfl

end EulerNonuniqueness.Paper
