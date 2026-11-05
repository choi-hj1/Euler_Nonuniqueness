import EulerNonuniqueness.Section6.ActualExternalCentroidDynamics

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem integrableOn_biotSavartKernel_of_separation {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    {position : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ domain, distance ≤ ‖position - source‖) :
    IntegrableOn (fun source => biotSavartKernel (position - source)) domain := by
  have constantIntegrable : IntegrableOn (fun _ : ℂ => 1 / (2 * Real.pi * distance)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have kernelMeasurable : Measurable (fun source : ℂ => biotSavartKernel (position - source)) :=
    measurable_biotSavartKernel.comp (measurable_const.sub measurable_id)
  apply constantIntegrable.mono' kernelMeasurable.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurable] with source member
  rw [norm_biotSavartKernel]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (mul_le_mul_of_nonneg_left (separated source member) (by positivity))

theorem biotSavartKernel_pair_separation_bound {first second source : ℂ} {distance : ℝ}
    (positive : 0 < distance) (firstSeparated : distance ≤ ‖first - source‖)
    (secondSeparated : distance ≤ ‖second - source‖) :
    ‖biotSavartKernel (first - source) - biotSavartKernel (second - source)‖ ≤
      ‖first - second‖ / (2 * Real.pi * distance ^ 2) := by
  rw [norm_biotSavartKernel_sub (norm_pos_iff.mp (positive.trans_le firstSeparated))
    (norm_pos_iff.mp (positive.trans_le secondSeparated))]
  have difference : (first - source) - (second - source) = first - second := by abel
  rw [difference]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  have product := mul_le_mul firstSeparated secondSeparated positive.le (norm_nonneg _)
  have multiplied := mul_le_mul_of_nonneg_left product (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith only [multiplied]

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem component_biotSavart_difference_bound (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (source : Fin count)
    {first second : ℂ} {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ position ∈ flow.domain time source, distance ≤ ‖first - position‖)
    (secondSeparated : ∀ position ∈ flow.domain time source, distance ≤ ‖second - position‖) :
    ‖biotSavart (flow.componentVorticity time source) first -
        biotSavart (flow.componentVorticity time source) second‖ ≤
      (|configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
        (2 * Real.pi * distance ^ 2)) * ‖first - second‖ := by
  have firstIntegrable := Section6.integrableOn_biotSavartKernel_of_separation
    (flow.domain_isOpen time source).measurableSet (flow.domain_isBounded time source).measure_lt_top positive firstSeparated
  have secondIntegrable := Section6.integrableOn_biotSavartKernel_of_separation
    (flow.domain_isOpen time source).measurableSet (flow.domain_isBounded time source).measure_lt_top positive secondSeparated
  have velocity (position : ℂ) : biotSavart (flow.componentVorticity time source) position =
      configuration.density source • (∫ location in flow.domain time source, biotSavartKernel (position - location)) :=
    Section6.biotSavart_indicator_density_integral (flow.domain_isOpen time source).measurableSet _ _
  rw [velocity first, velocity second, ← smul_sub, ← integral_sub firstIntegrable secondIntegrable, norm_smul, Real.norm_eq_abs]
  have estimate := norm_integral_le_of_norm_le
    (μ := volume.restrict (flow.domain time source))
    (f := fun position => biotSavartKernel (first - position) - biotSavartKernel (second - position))
    (g := fun _ : ℂ => ‖first - second‖ / (2 * Real.pi * distance ^ 2))
    (integrableOn_const.mpr (Or.inr (flow.domain_isBounded time source).measure_lt_top)) (by
      filter_upwards [ae_restrict_mem (flow.domain_isOpen time source).measurableSet] with position member
      exact Section6.biotSavartKernel_pair_separation_bound positive (firstSeparated position member) (secondSeparated position member))
  have area : (volume.restrict (flow.domain time source)).real univ = Real.pi * configuration.radius source ^ 2 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using flow.domain_area inside source
  rw [integral_const, area, smul_eq_mul] at estimate
  apply (mul_le_mul_of_nonneg_left estimate (abs_nonneg (configuration.density source))).trans_eq
  rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * configuration.radius source ^ 2 by positivity)]
  ring

theorem component_biotSavart_lipschitz_on (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (source : Fin count)
    (region : Set ℂ) {distance : ℝ} (positive : 0 < distance) {bound : ℝ≥0}
    (separated : ∀ position ∈ region, ∀ location ∈ flow.domain time source, distance ≤ ‖position - location‖)
    (boundLarge : |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
      (2 * Real.pi * distance ^ 2) ≤ bound) :
    LipschitzOnWith bound (biotSavart (flow.componentVorticity time source)) region := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstMember second secondMember
  exact (flow.component_biotSavart_difference_bound inside source positive
    (separated first firstMember) (separated second secondMember)).trans
      (mul_le_mul_of_nonneg_right boundLarge (norm_nonneg _))

theorem subfamilyExternalPatchField_lipschitz_on (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (region : Set ℂ) (distance : Fin count → ℝ) {bound : ℝ≥0}
    (positive : ∀ source ∈ Finset.univ \ selected, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ \ selected, ∀ position ∈ region,
      ∀ location ∈ flow.domain time source, distance source ≤ ‖position - location‖)
    (boundLarge : (∑ source ∈ Finset.univ \ selected,
      |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
        (2 * Real.pi * distance source ^ 2)) ≤ (bound : ℝ)) :
    LipschitzOnWith bound (flow.subfamilyExternalPatchField selected time) region := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstMember second secondMember
  unfold subfamilyExternalPatchField
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ source ∈ Finset.univ \ selected,
        (|configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
          (2 * Real.pi * distance source ^ 2)) * ‖first - second‖ := by
      apply Finset.sum_le_sum
      intro source member
      exact flow.component_biotSavart_difference_bound inside source (positive source member)
        (separated source member first firstMember) (separated source member second secondMember)
    _ = (∑ source ∈ Finset.univ \ selected,
        |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
          (2 * Real.pi * distance source ^ 2)) * ‖first - second‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right boundLarge (norm_nonneg _)

theorem subfamilyExternalPatchField_lipschitz_on_ball (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (receiverCenter : ℂ) (receiverRadius : ℝ) {bound : ℝ≥0}
    (sourceBounded : ∀ source ∈ Finset.univ \ selected,
      flow.domain time source ⊆ Metric.closedBall (flow.centroid time source) (2 * configuration.radius source))
    (receiverSmall : ∀ source ∈ Finset.univ \ selected,
      4 * receiverRadius ≤ ‖receiverCenter - flow.centroid time source‖)
    (sourceSmall : ∀ source ∈ Finset.univ \ selected,
      8 * configuration.radius source ≤ ‖receiverCenter - flow.centroid time source‖)
    (boundLarge : (∑ source ∈ Finset.univ \ selected,
      2 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| /
        (Real.pi * ‖receiverCenter - flow.centroid time source‖ ^ 2)) ≤ (bound : ℝ)) :
    LipschitzOnWith bound (flow.subfamilyExternalPatchField selected time)
      (Metric.closedBall receiverCenter receiverRadius) := by
  apply flow.subfamilyExternalPatchField_lipschitz_on selected inside _
    (fun source => ‖receiverCenter - flow.centroid time source‖ / 2)
  · intro source member
    have large := sourceSmall source member
    have positive := lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 8) (configuration.radius_pos source)) large
    exact div_pos positive (by norm_num)
  · intro source member position positionMember location locationMember
    have positionBound : ‖position - receiverCenter‖ ≤ receiverRadius := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using positionMember
    have locationBound : ‖location - flow.centroid time source‖ ≤ 2 * configuration.radius source := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using sourceBounded source member locationMember
    have triangle : ‖receiverCenter - flow.centroid time source‖ ≤
        ‖position - receiverCenter‖ + ‖position - location‖ + ‖location - flow.centroid time source‖ := by
      have first := norm_add_le (receiverCenter - position) (position - location)
      have second := norm_add_le (receiverCenter - location) (location - flow.centroid time source)
      rw [sub_add_sub_cancel] at first second
      have normFlip : ‖receiverCenter - position‖ = ‖position - receiverCenter‖ := norm_sub_rev _ _
      rw [normFlip] at first
      linarith
    linarith [receiverSmall source member, sourceSmall source member]
  · apply le_trans _ boundLarge
    apply Finset.sum_le_sum
    intro source _
    exact le_of_eq (by ring)

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
