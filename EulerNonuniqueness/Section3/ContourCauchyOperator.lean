import EulerNonuniqueness.Section3.ContourCauchyGlobalHolder

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem banachContourCauchy_density_integrable_centered (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    IntervalIntegrable (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target)
      volume (target - Real.pi) (target + Real.pi) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi)).mpr
  apply contourCauchyDensityRemainder_integrable_interval (norm_nonneg density) (norm_nonneg data)
    (sub_pos.mpr (small.trans_le (min_le_right _ _)))
    data.val.1.continuous data.val.2.val.1.continuous density.val.1.continuous
    (fun source _ => PeriodicHolderHalf.holder_bound density source target)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data source)
  intro source membership
  apply PeriodicC1HolderHalf.chord_bound_extended data
  rw [abs_le]
  constructor <;> linarith [membership.1, membership.2, Real.pi_pos]

theorem contourCauchyOperator_add (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (first second : PeriodicHolderHalf) :
    contourCauchyOperator data small (first + second) =
      contourCauchyOperator data small first + contourCauchyOperator data small second := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change contourCauchyTransform data.val.1 data.val.2.val.1 (first + second).val.1 target =
    contourCauchyTransform data.val.1 data.val.2.val.1 first.val.1 target +
      contourCauchyTransform data.val.1 data.val.2.val.1 second.val.1 target
  have identity : contourCauchyDensityRemainder data.val.1 data.val.2.val.1 (first + second).val.1 target =
      (fun source => contourCauchyDensityRemainder data.val.1 data.val.2.val.1 first.val.1 target source +
        contourCauchyDensityRemainder data.val.1 data.val.2.val.1 second.val.1 target source) := by
    funext source
    unfold contourCauchyDensityRemainder
    change ((first.val.1 source + second.val.1 source) - (first.val.1 target + second.val.1 target)) * _ / _ = _
    ring
  unfold contourCauchyTransform
  rw [identity, intervalIntegral.integral_add
    (banachContourCauchy_density_integrable_centered data first small target)
    (banachContourCauchy_density_integrable_centered data second small target)]
  change _ - (Real.pi : ℂ) * Complex.I * (first.val.1 target + second.val.1 target) = _
  ring

theorem contourCauchyOperator_smul (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (scalar : ℝ) (density : PeriodicHolderHalf) :
    contourCauchyOperator data small (scalar • density) = scalar • contourCauchyOperator data small density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change contourCauchyTransform data.val.1 data.val.2.val.1 (scalar • density).val.1 target =
    scalar • contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 target
  have identity : contourCauchyDensityRemainder data.val.1 data.val.2.val.1 (scalar • density).val.1 target =
      (fun source => scalar • contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source) := by
    funext source
    unfold contourCauchyDensityRemainder
    change ((scalar • density.val.1 source) - (scalar • density.val.1 target)) * _ / _ = _
    simp only [Complex.real_smul]
    ring
  unfold contourCauchyTransform
  rw [identity, intervalIntegral.integral_smul]
  change scalar • _ - (Real.pi : ℂ) * Complex.I * (scalar • density.val.1 target) = scalar • _
  simp only [Complex.real_smul]
  ring

def contourCauchyOperatorCLM (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous
    { toFun := contourCauchyOperator data small
      map_add' := contourCauchyOperator_add data small
      map_smul' := contourCauchyOperator_smul data small }
    (max (contourCauchySupConstant data) (contourCauchyGlobalHolderConstant data))
    (contourCauchyOperator_norm_bound data small)

theorem contourCauchyOperatorCLM_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (density : PeriodicHolderHalf) (target : ℝ) :
    (contourCauchyOperatorCLM data small density).val.1 target =
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 target := rfl

end

end EulerNonuniqueness.Paper
