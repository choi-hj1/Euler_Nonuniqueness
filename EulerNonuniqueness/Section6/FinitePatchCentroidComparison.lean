import EulerNonuniqueness.Section6.PatchPairComparison

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem external_pair_centroid_comparison (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (receiver source : Fin count) {sourceRadius receiverRadius : ℝ}
    (sourceBounded : flow.domain time source ⊆ Metric.closedBall (flow.centroid time source) sourceRadius)
    (receiverBounded : flow.domain time receiver ⊆ Metric.closedBall (flow.centroid time receiver) receiverRadius)
    (distancePositive : 0 < ‖flow.centroid time receiver - flow.centroid time source‖)
    (sourceSmall : 4 * sourceRadius ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    (receiverSmall : 2 * receiverRadius ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖(Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver,
          biotSavart ((flow.domain time source).indicator (fun _ => configuration.density source)) position) -
        (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
          biotSavartKernel (flow.centroid time receiver - flow.centroid time source)‖ ≤
      |configuration.density source| * (Real.pi * configuration.radius source ^ 2) *
        (8 * sourceRadius ^ 2 + receiverRadius ^ 2) /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  have pair := Section6.patch_pair_centroid_comparison
    (sourceDomain := flow.domain time source) (receiverDomain := flow.domain time receiver)
    (sourceCenter := flow.centroid time source) (receiverCenter := flow.centroid time receiver)
    (sourceRadius := sourceRadius) (receiverRadius := receiverRadius)
    (flow.domain_isOpen time source).measurableSet (flow.domain_isOpen time receiver).measurableSet
    sourceBounded receiverBounded (flow.domain_centroid_centered_integral inside source)
    (flow.domain_centroid_centered_integral inside receiver) distancePositive sourceSmall receiverSmall
    (configuration.density source)
  have sourceArea : volume.real (flow.domain time source) = Real.pi * configuration.radius source ^ 2 :=
    flow.domain_area inside source
  have receiverArea : volume.real (flow.domain time receiver) = Real.pi * configuration.radius receiver ^ 2 :=
    flow.domain_area inside receiver
  rw [sourceArea, receiverArea] at pair
  have areaPositive : 0 < Real.pi * configuration.radius receiver ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos (configuration.radius_pos receiver))
  have normalized := mul_le_mul_of_nonneg_left pair (inv_nonneg.mpr areaPositive.le)
  have cancellation :
      (Real.pi * configuration.radius receiver ^ 2)⁻¹ *
        (configuration.density source * (Real.pi * configuration.radius source ^ 2) *
          (Real.pi * configuration.radius receiver ^ 2)) =
      configuration.density source * (Real.pi * configuration.radius source ^ 2) := by
    field_simp
  rw [← Real.norm_of_nonneg (inv_nonneg.mpr areaPositive.le), ← norm_smul,
    smul_sub, smul_smul, cancellation] at normalized
  rw [Real.norm_of_nonneg (inv_nonneg.mpr areaPositive.le)] at normalized
  apply normalized.trans_eq
  field_simp [ne_of_gt areaPositive, Real.pi_ne_zero, ne_of_gt distancePositive,
    ne_of_gt (configuration.radius_pos receiver)]
  <;> ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
