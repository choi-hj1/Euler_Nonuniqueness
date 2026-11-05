import EulerNonuniqueness.Section6.ActualPatchFieldLipschitz

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem component_biotSavart_norm_le_of_separation (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (source : Fin count)
    {position : ℂ} {distance : ℝ} (distancePositive : 0 < distance)
    (separated : ∀ location ∈ flow.domain time source, distance ≤ ‖position - location‖) :
    ‖biotSavart (flow.componentVorticity time source) position‖ ≤
      |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
        (2 * Real.pi * distance) := by
  have velocity : biotSavart (flow.componentVorticity time source) position =
      configuration.density source •
        (∫ location in flow.domain time source, biotSavartKernel (position - location)) :=
    Section6.biotSavart_indicator_density_integral (flow.domain_isOpen time source).measurableSet _ _
  have estimate := norm_integral_le_of_norm_le
    (μ := volume.restrict (flow.domain time source))
    (f := fun location => biotSavartKernel (position - location))
    (g := fun _ : ℂ => 1 / (2 * Real.pi * distance))
    (integrableOn_const.mpr (Or.inr (flow.domain_isBounded time source).measure_lt_top)) (by
      filter_upwards [ae_restrict_mem (flow.domain_isOpen time source).measurableSet] with location member
      rw [norm_biotSavartKernel]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left (separated location member) (by positivity)))
  have area : (volume.restrict (flow.domain time source)).real univ = Real.pi * configuration.radius source ^ 2 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using flow.domain_area inside source
  rw [integral_const, area, smul_eq_mul] at estimate
  rw [velocity, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left estimate (abs_nonneg (configuration.density source))).trans_eq (by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * configuration.radius source ^ 2 by positivity)]
    ring)

theorem subfamilyExternalPatchField_norm_le_of_separation (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (position : ℂ) (distance : Fin count → ℝ)
    (distancePositive : ∀ source ∈ Finset.univ \ selected, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ \ selected, ∀ location ∈ flow.domain time source,
      distance source ≤ ‖position - location‖) :
    ‖flow.subfamilyExternalPatchField selected time position‖ ≤
      ∑ source ∈ Finset.univ \ selected,
        |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
          (2 * Real.pi * distance source) := by
  unfold subfamilyExternalPatchField
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source member
  exact flow.component_biotSavart_norm_le_of_separation inside source
    (distancePositive source member) (separated source member)

theorem subfamilyExternalPatchField_norm_le_on_ball (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (center : ℂ) {radius distance : ℝ} (distancePositive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ \ selected, ∀ location ∈ flow.domain time source,
      radius + distance ≤ ‖center - location‖)
    {position : ℂ} (positionInside : position ∈ Metric.closedBall center radius) :
    ‖flow.subfamilyExternalPatchField selected time position‖ ≤
      (∑ source ∈ Finset.univ \ selected,
        |configuration.density source * (Real.pi * configuration.radius source ^ 2)|) /
          (2 * Real.pi * distance) := by
  have estimate := flow.subfamilyExternalPatchField_norm_le_of_separation selected inside position
    (fun _ => distance) (fun _ _ => distancePositive) (by
      intro source member location locationMember
      have triangle := norm_sub_le (center - location) (position - location)
      have difference : center - location - (position - location) = center - position := by abel
      rw [difference, norm_sub_rev center position] at triangle
      have positionBound : ‖position - center‖ ≤ radius := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using positionInside
      have secondTriangle := norm_add_le (center - position) (position - location)
      rw [sub_add_sub_cancel, norm_sub_rev center position] at secondTriangle
      linarith [separated source member location locationMember])
  simpa only [Finset.sum_div] using estimate

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
