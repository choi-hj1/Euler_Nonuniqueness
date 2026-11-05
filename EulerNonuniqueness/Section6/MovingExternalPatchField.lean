import EulerNonuniqueness.Section6.MovingPatchFieldBounds

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper

def externalPatchVorticity {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : Vorticity :=
  fun position => ∑ source ∈ Finset.univ.erase index, quadrupoleDensity scales motion time source position

theorem FinitePatchEvolution.patch_biotSavart_integrand_integrable
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) (position : ℂ) :
    Integrable (fun source => patchDensity scales motion time index patch source •
      biotSavartKernel (position - source)) := by
  have properties := evolution.2.2.2.1 time inside index patch
  apply integrable_biotSavart_integrand_of_L1_L4
  · exact patchDensity_integrable scales motion time index patch properties.1 properties.2.1
  · exact memLp_indicator_const _ properties.1.measurableSet _ (Or.inr properties.2.1.measure_lt_top.ne)

theorem FinitePatchEvolution.quadrupole_biotSavart_eq_sum_patch
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (position : ℂ) :
    biotSavart (quadrupoleDensity scales motion time index) position =
      ∑ patch : Fin 4, biotSavart (patchDensity scales motion time index patch) position := by
  simp only [biotSavart, quadrupoleDensity, Finset.sum_smul]
  exact integral_finset_sum _ (fun patch _ => evolution.patch_biotSavart_integrand_integrable inside index patch position)

theorem FinitePatchEvolution.externalPatch_biotSavart_eq_sum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (position : ℂ) :
    biotSavart (externalPatchVorticity scales motion time index) position =
      ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        biotSavart (patchDensity scales motion time source patch) position := by
  have integrable (source : Fin count) :
      Integrable (fun location => quadrupoleDensity scales motion time source location •
        biotSavartKernel (position - location)) := by
    simp only [quadrupoleDensity, Finset.sum_smul]
    exact integrable_finset_sum _ (fun patch _ => evolution.patch_biotSavart_integrand_integrable inside source patch position)
  change (∫ location, (∑ source ∈ Finset.univ.erase index,
    quadrupoleDensity scales motion time source location) • biotSavartKernel (position - location)) = _
  simp_rw [Finset.sum_smul]
  rw [integral_finset_sum _ (fun source _ => integrable source)]
  exact Finset.sum_congr rfl (fun source _ => evolution.quadrupole_biotSavart_eq_sum_patch inside source position)

theorem FinitePatchEvolution.externalPatch_biotSavart_bounds
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
    ‖biotSavart (externalPatchVorticity scales motion time index) first‖ ≤
        ∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) / (Real.pi * distance source) ∧
      ‖biotSavart (externalPatchVorticity scales motion time index) first -
          biotSavart (externalPatchVorticity scales motion time index) second‖ ≤
        (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) * ‖first - second‖ := by
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :=
    evolution.patch_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive source patch
      (positive source member) (firstSeparated source member patch) (secondSeparated source member patch)
  rw [evolution.externalPatch_biotSavart_eq_sum inside index first,
    evolution.externalPatch_biotSavart_eq_sum inside index second]
  constructor
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro source member
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => (individual source member patch).1)).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring))
  · rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro source member
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => (individual source member patch).2)).trans_eq
      (by simp only [Fin.sum_univ_succ]; ring))

theorem FinitePatchEvolution.externalPatch_biotSavart_lipschitzOn
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    (region : Set ℂ) {bound : ℝ≥0}
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ region, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ motion.domain time source patch, distance source ≤ ‖position - location‖)
    (boundLarge : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (bound : ℝ)) :
    LipschitzOnWith bound (biotSavart (externalPatchVorticity scales motion time index)) region := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstInside second secondInside
  exact (evolution.externalPatch_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive
    index distance positive (separated first firstInside) (separated second secondInside)).2.trans
      (mul_le_mul_of_nonneg_right boundLarge (norm_nonneg _))

theorem FinitePatchEvolution.externalPatch_biotSavart_bounds_on_balls
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (sourceCenter : Fin count → ℂ) (sourceRadius distance : Fin count → ℝ)
    (center : ℂ) (radius : ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceInside : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (sourceCenter source) (sourceRadius source))
    (gap : ∀ source ∈ Finset.univ.erase index,
      radius + sourceRadius source + distance source ≤ ‖center - sourceCenter source‖)
    {first second : ℂ} (firstInside : first ∈ Metric.closedBall center radius)
    (secondInside : second ∈ Metric.closedBall center radius) :
    ‖biotSavart (externalPatchVorticity scales motion time index) first‖ ≤
        ∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) / (Real.pi * distance source) ∧
      ‖biotSavart (externalPatchVorticity scales motion time index) first -
          biotSavart (externalPatchVorticity scales motion time index) second‖ ≤
        (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) * ‖first - second‖ := by
  have separation (position : ℂ) (positionInside : position ∈ Metric.closedBall center radius)
      (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4)
      (location : ℂ) (locationInside : location ∈ motion.domain time source patch) :
      distance source ≤ ‖position - location‖ := by
    have receiverBound : ‖position - center‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using positionInside
    have sourceBound : ‖location - sourceCenter source‖ ≤ sourceRadius source := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceInside source member patch locationInside
    have triangle := norm_add_le (center - position) (position - location)
    have triangleSecond := norm_add_le (center - location) (location - sourceCenter source)
    rw [sub_add_sub_cancel, norm_sub_rev center position] at triangle
    rw [sub_add_sub_cancel] at triangleSecond
    linarith [gap source member]
  exact evolution.externalPatch_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive
    index distance positive (separation first firstInside) (separation second secondInside)

end EulerNonuniqueness.Paper
