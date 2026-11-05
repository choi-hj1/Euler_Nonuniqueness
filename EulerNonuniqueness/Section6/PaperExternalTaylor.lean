import EulerNonuniqueness.Section6.MovingExternalPatchDerivative

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_biotSavart_fderiv_taylor_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (patch : Fin 4)
    {center position : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ motion.domain time index patch, distance ≤ ‖center - source‖)
    (near : 2 * ‖position - center‖ ≤ distance) :
    ‖biotSavart (patchDensity scales motion time index patch) position -
        biotSavart (patchDensity scales motion time index patch) center -
        fderiv ℝ (biotSavart (patchDensity scales motion time index patch)) center (position - center)‖ ≤
      scales.circulation (index.val + 1) * ‖position - center‖ ^ 2 / (Real.pi * distance ^ 3) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have derivative := Section6.indicator_biotSavart_hasFDerivAt_of_separation properties.1.measurableSet
    properties.2.1.measure_lt_top (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    positive separated
  have estimate := Section6.indicator_biotSavart_strain_taylor_bound properties.1.measurableSet
    properties.2.1.measure_lt_top (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    positive separated near
  change ‖biotSavart (patchDensity scales motion time index patch) position -
      biotSavart (patchDensity scales motion time index patch) center - _‖ ≤ _ at estimate
  rw [evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive index patch] at estimate
  have derivativeIdentity : fderiv ℝ (biotSavart (patchDensity scales motion time index patch)) center =
      ((patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        ∫ source in motion.domain time index patch, Section6.biotSavartKernelStrain center source) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) := derivative.fderiv
  rw [derivativeIdentity]
  exact estimate

theorem FinitePatchEvolution.externalPatch_biotSavart_fderiv_taylor_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    {center position : ℂ}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖center - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * ‖position - center‖ ≤ distance source) :
    ‖biotSavart (externalPatchVorticity scales motion time index) position -
        biotSavart (externalPatchVorticity scales motion time index) center -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (position - center)‖ ≤
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * ‖position - center‖ ^ 2 := by
  rw [(evolution.externalPatch_biotSavart_hasFDerivAt inside index distance positive separated).fderiv,
    evolution.externalPatch_biotSavart_eq_sum inside index position,
    evolution.externalPatch_biotSavart_eq_sum inside index center]
  have expansion :
      (∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4, biotSavart (patchDensity scales motion time source patch) position) -
        (∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4, biotSavart (patchDensity scales motion time source patch) center) -
        (∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
          fderiv ℝ (biotSavart (patchDensity scales motion time source patch)) center) (position - center) =
      ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        (biotSavart (patchDensity scales motion time source patch) position -
          biotSavart (patchDensity scales motion time source patch) center -
          fderiv ℝ (biotSavart (patchDensity scales motion time source patch)) center (position - center)) := by
    simp only [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]
  rw [expansion, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source member
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun patch _ => evolution.patch_biotSavart_fderiv_taylor_bound inside
    amplitudePositive frequencyPositive ratioPositive source patch (positive source member)
    (separated source member patch) (near source member))).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring)

end EulerNonuniqueness.Paper
