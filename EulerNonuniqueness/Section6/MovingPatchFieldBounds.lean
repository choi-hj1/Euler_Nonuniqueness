import EulerNonuniqueness.Section6.ActualPatchFieldLipschitz
import EulerNonuniqueness.Section3.PatchStaticMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem indicator_biotSavart_norm_bound {domain : Set ℂ} (measurable : MeasurableSet domain)
    (finite : volume domain < ⊤) (density : ℝ) {position : ℂ} {distance : ℝ}
    (positive : 0 < distance) (separated : ∀ source ∈ domain, distance ≤ ‖position - source‖) :
    ‖biotSavart (domain.indicator (fun _ => density)) position‖ ≤
      |density| * volume.real domain / (2 * Real.pi * distance) := by
  rw [biotSavart_indicator_density_integral measurable, norm_smul, Real.norm_eq_abs]
  have estimate := norm_integral_le_of_norm_le (μ := volume.restrict domain)
    (f := fun source => biotSavartKernel (position - source))
    (g := fun _ : ℂ => 1 / (2 * Real.pi * distance))
    (integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      rw [norm_biotSavartKernel]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left (separated source member) (by positivity)))
  rw [integral_const] at estimate
  apply (mul_le_mul_of_nonneg_left estimate (abs_nonneg density)).trans_eq
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  ring

theorem indicator_biotSavart_difference_bound {domain : Set ℂ} (measurable : MeasurableSet domain)
    (finite : volume domain < ⊤) (density : ℝ) {first second : ℂ} {distance : ℝ}
    (positive : 0 < distance)
    (firstSeparated : ∀ source ∈ domain, distance ≤ ‖first - source‖)
    (secondSeparated : ∀ source ∈ domain, distance ≤ ‖second - source‖) :
    ‖biotSavart (domain.indicator (fun _ => density)) first -
        biotSavart (domain.indicator (fun _ => density)) second‖ ≤
      (|density| * volume.real domain / (2 * Real.pi * distance ^ 2)) * ‖first - second‖ := by
  have firstIntegrable := integrableOn_biotSavartKernel_of_separation measurable finite positive firstSeparated
  have secondIntegrable := integrableOn_biotSavartKernel_of_separation measurable finite positive secondSeparated
  rw [biotSavart_indicator_density_integral measurable, biotSavart_indicator_density_integral measurable,
    ← smul_sub, ← integral_sub firstIntegrable secondIntegrable, norm_smul, Real.norm_eq_abs]
  have estimate := norm_integral_le_of_norm_le (μ := volume.restrict domain)
    (f := fun source => biotSavartKernel (first - source) - biotSavartKernel (second - source))
    (g := fun _ : ℂ => ‖first - second‖ / (2 * Real.pi * distance ^ 2))
    (integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      exact biotSavartKernel_pair_separation_bound positive (firstSeparated source member) (secondSeparated source member))
  rw [integral_const] at estimate
  apply (mul_le_mul_of_nonneg_left estimate (abs_nonneg density)).trans_eq
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_biotSavart_bounds
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (patch : Fin 4)
    {first second : ℂ} {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖first - source‖)
    (secondSeparated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖second - source‖) :
    ‖biotSavart (patchDensity scales motion time index patch) first‖ ≤
        scales.circulation (index.val + 1) / (2 * Real.pi * distance) ∧
      ‖biotSavart (patchDensity scales motion time index patch) first -
          biotSavart (patchDensity scales motion time index patch) second‖ ≤
        (scales.circulation (index.val + 1) / (2 * Real.pi * distance ^ 2)) * ‖first - second‖ := by
  have properties := evolution.2.2.2.1 time inside index patch
  let density := patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  have mass : |density| * volume.real (motion.domain time index patch) = scales.circulation (index.val + 1) := by
    have sign : |patchSign patch| = 1 := by fin_cases patch <;> norm_num [patchSign]
    have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
      rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
    rw [area]
    dsimp only [density]
    rw [abs_mul, abs_mul, sign, one_mul, abs_of_pos amplitudePositive, abs_pow,
      abs_of_pos (scales.omega_pos frequencyPositive ratioPositive _), ← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive]
    ring
  constructor
  · have estimate := Section6.indicator_biotSavart_norm_bound properties.1.measurableSet
      properties.2.1.measure_lt_top density positive firstSeparated
    rw [mass] at estimate
    exact estimate
  · have estimate := Section6.indicator_biotSavart_difference_bound properties.1.measurableSet
      properties.2.1.measure_lt_top density positive firstSeparated secondSeparated
    rw [mass] at estimate
    exact estimate

end EulerNonuniqueness.Paper
