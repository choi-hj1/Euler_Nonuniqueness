import EulerNonuniqueness.Section6.PaperPatchCentroidAlgebra

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupoleDensity_integrable
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon) (index : Fin count) :
    Integrable (quadrupoleDensity scales motion time index) := by
  apply integrable_finset_sum
  intro patch _
  have properties := evolution.2.2.2.1 time inside index patch
  exact patchDensity_integrable scales motion time index patch properties.1 properties.2.1

theorem FinitePatchEvolution.quadrupoleDensity_integral_abs_le
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    (∫ position, |quadrupoleDensity scales motion time index position|) ≤ 4 * scales.circulation (index.val + 1) := by
  have patchIntegrable (patch : Fin 4) : Integrable (patchDensity scales motion time index patch) := by
    have properties := evolution.2.2.2.1 time inside index patch
    exact patchDensity_integrable scales motion time index patch properties.1 properties.2.1
  have patchMass (patch : Fin 4) : (∫ position, |patchDensity scales motion time index patch position|) =
      scales.circulation (index.val + 1) := by
    have identity : (fun position => |patchDensity scales motion time index patch position|) =
        (motion.domain time index patch).indicator
          (fun _ => |patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4|) := by
      funext position
      by_cases member : position ∈ motion.domain time index patch <;> simp [patchDensity, member]
    rw [identity, integral_indicator_const _ (evolution.2.2.2.1 time inside index patch).1.measurableSet]
    exact (mul_comm _ _).trans (evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive index patch)
  have estimate := integral_mono_ae (evolution.quadrupoleDensity_integrable inside index).norm
    (integrable_finset_sum _ (fun patch _ => (patchIntegrable patch).norm)) (Filter.Eventually.of_forall
      (fun position => norm_sum_le (s := Finset.univ) (fun patch => patchDensity scales motion time index patch position)))
  simp only [Real.norm_eq_abs] at estimate
  have absSumIntegral : (∫ position, ∑ patch : Fin 4, |patchDensity scales motion time index patch position|) =
      ∑ patch : Fin 4, ∫ position, |patchDensity scales motion time index patch position| :=
    integral_finset_sum _ (fun patch _ => by simpa only [Real.norm_eq_abs] using (patchIntegrable patch).norm)
  rw [absSumIntegral] at estimate
  simpa only [Real.norm_eq_abs, patchMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] using estimate

theorem FinitePatchEvolution.integral_quadrupoleDensity_first_moment
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center : ℂ) :
    (∫ position, quadrupoleDensity scales motion time index position • (position - center)) =
      (4 * scales.circulation (index.val + 1)) • centroidAsymmetry motion time index := by
  have patchMoment (patch : Fin 4) :
      (∫ position in motion.domain time index patch, position - center) =
      (Real.pi * scales.radius (index.val + 1) ^ 2) • (patchCentroid motion time index patch - center) := by
    have properties := evolution.2.2.2.1 time inside index patch
    have finite : volume (motion.domain time index patch) < ⊤ := properties.2.1.measure_lt_top
    have coordinateIntegrable : IntegrableOn (fun position : ℂ => position - patchCentroid motion time index patch)
        (motion.domain time index patch) :=
      (((continuous_id.sub continuous_const).continuousOn.integrableOn_compact properties.2.1.isCompact_closure).mono_set subset_closure)
    have constantIntegrable : IntegrableOn (fun _ : ℂ => patchCentroid motion time index patch - center)
        (motion.domain time index patch) := integrableOn_const.mpr (Or.inr finite)
    have expansion : (fun position : ℂ => position - center) =
        fun position => (position - patchCentroid motion time index patch) + (patchCentroid motion time index patch - center) := by
      funext position
      abel
    rw [expansion, integral_add coordinateIntegrable constantIntegrable,
      evolution.patch_centroid_centered_integral_zero inside index patch, zero_add, integral_const]
    have area : (volume.restrict (motion.domain time index patch)).real univ = Real.pi * scales.radius (index.val + 1) ^ 2 := by
      rw [Measure.real, Measure.restrict_apply_univ, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
    rw [area]
  have mass (patch : Fin 4) : (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
      (Real.pi * scales.radius (index.val + 1) ^ 2) = patchSign patch * scales.circulation (index.val + 1) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    ring
  rw [evolution.integral_quadrupoleDensity_smul_continuous inside index
    (function := fun position : ℂ => position - center) (continuous_id.sub continuous_const)]
  simp_rw [patchMoment, smul_smul, mass]
  simp only [Fin.sum_univ_succ, patchSign, Fin.val_zero, Fin.val_succ, centroidAsymmetry, Complex.real_smul]
  norm_num
  push_cast
  ring

end EulerNonuniqueness.Paper
