import EulerNonuniqueness.Section6.MovingExternalPatchField
import EulerNonuniqueness.Section6.MovingPatchHessian

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_abs_density_mul_area
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (patch : Fin 4) :
    |patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4| *
      volume.real (motion.domain time index patch) = scales.circulation (index.val + 1) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have sign : |patchSign patch| = 1 := by fin_cases patch <;> norm_num [patchSign]
  have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  rw [area, abs_mul, abs_mul, sign, one_mul, abs_of_pos amplitudePositive, abs_pow,
    abs_of_pos (scales.omega_pos frequencyPositive ratioPositive _),
    ← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive]
  ring

theorem FinitePatchEvolution.patch_biotSavart_hasFDerivAt_of_separation
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) {center : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖center - source‖) :
    HasFDerivAt (biotSavart (patchDensity scales motion time index patch))
      (fderiv ℝ (biotSavart (patchDensity scales motion time index patch)) center) center := by
  have properties := evolution.2.2.2.1 time inside index patch
  exact (Section6.indicator_biotSavart_hasFDerivAt_of_separation properties.1.measurableSet
    properties.2.1.measure_lt_top (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    positive separated).differentiableAt.hasFDerivAt

theorem FinitePatchEvolution.patch_biotSavart_fderiv_difference_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (patch : Fin 4)
    {first second : ℂ} {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖first - source‖)
    (secondSeparated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖second - source‖) :
    ‖fderiv ℝ (biotSavart (patchDensity scales motion time index patch)) first -
        fderiv ℝ (biotSavart (patchDensity scales motion time index patch)) second‖ ≤
      scales.circulation (index.val + 1) * ‖first - second‖ / (Real.pi * distance ^ 3) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have estimate := Section6.indicator_biotSavart_fderiv_difference_bound properties.1.measurableSet
    properties.2.1.measure_lt_top (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    positive firstSeparated secondSeparated
  rw [evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive index patch] at estimate
  exact estimate

theorem FinitePatchEvolution.externalPatch_biotSavart_hasFDerivAt
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (distance : Fin count → ℝ) {center : ℂ}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖center - location‖) :
    HasFDerivAt (biotSavart (externalPatchVorticity scales motion time index))
      (∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        fderiv ℝ (biotSavart (patchDensity scales motion time source patch)) center) center := by
  have identity : biotSavart (externalPatchVorticity scales motion time index) =
      fun position => ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        biotSavart (patchDensity scales motion time source patch) position :=
    funext (evolution.externalPatch_biotSavart_eq_sum inside index)
  rw [identity]
  exact HasFDerivAt.sum (fun source member => HasFDerivAt.sum (fun patch _ =>
    evolution.patch_biotSavart_hasFDerivAt_of_separation inside source patch
      (positive source member) (separated source member patch)))

theorem FinitePatchEvolution.externalPatch_biotSavart_fderiv_difference_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    {first second : ℂ}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (firstSeparated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖first - location‖)
    (secondSeparated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖second - location‖) :
    ‖fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) first -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) second‖ ≤
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * ‖first - second‖ := by
  rw [(evolution.externalPatch_biotSavart_hasFDerivAt inside index distance positive firstSeparated).fderiv,
    (evolution.externalPatch_biotSavart_hasFDerivAt inside index distance positive secondSeparated).fderiv,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source member
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun patch _ => evolution.patch_biotSavart_fderiv_difference_bound
    inside amplitudePositive frequencyPositive ratioPositive source patch (positive source member)
    (firstSeparated source member patch) (secondSeparated source member patch))).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring)

theorem FinitePatchEvolution.externalPatch_biotSavart_fderiv_lipschitzOn
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    (region : Set ℂ) {bound : ℝ≥0}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ region, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ motion.domain time source patch, distance source ≤ ‖position - location‖)
    (boundLarge : (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) ≤ (bound : ℝ)) :
    LipschitzOnWith bound (fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index))) region := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstInside second secondInside
  exact (evolution.externalPatch_biotSavart_fderiv_difference_bound inside amplitudePositive frequencyPositive ratioPositive
    index distance positive (separated first firstInside) (separated second secondInside)).trans
      (mul_le_mul_of_nonneg_right boundLarge (norm_nonneg _))

end EulerNonuniqueness.Paper
