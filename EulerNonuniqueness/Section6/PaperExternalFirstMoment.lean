import EulerNonuniqueness.Section6.PaperExternalReceiverResidual

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_external_integral_eq_centroid_residual_sum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    (∫ position, quadrupoleDensity scales motion time index position •
      biotSavart (externalPatchVorticity scales motion time index) position) =
      scales.circulation (index.val + 1) • ∑ patch : Fin 4, patchSign patch •
        (biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch) +
          quadrupoleExternalReceiverResidual scales motion time index patch) := by
  classical
  have fieldIntegrable (receiver : Fin 4) :
      IntegrableOn (biotSavart (externalPatchVorticity scales motion time index))
        (motion.domain time index receiver) := by
    have identity : biotSavart (externalPatchVorticity scales motion time index) =
        fun position => ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
          biotSavart (patchDensity scales motion time source patch) position :=
      funext fun position => evolution.externalPatch_biotSavart_eq_sum inside index position
    rw [identity]
    exact integrable_finset_sum _ (fun source _ => integrable_finset_sum _
      (fun patch _ => evolution.patch_velocity_integrableOn_patch inside index source receiver patch))
  have weightedIntegrable (patch : Fin 4) : Integrable (fun position =>
      patchDensity scales motion time index patch position •
        biotSavart (externalPatchVorticity scales motion time index) position) := by
    have identity : (fun position => patchDensity scales motion time index patch position •
        biotSavart (externalPatchVorticity scales motion time index) position) =
        fun position => (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
          (motion.domain time index patch).indicator
            (biotSavart (externalPatchVorticity scales motion time index)) position := by
      funext position
      by_cases member : position ∈ motion.domain time index patch <;> simp [patchDensity, member]
    rw [identity]
    exact ((integrable_indicator_iff (evolution.2.2.2.1 time inside index patch).1.measurableSet).mpr
      (fieldIntegrable patch)).smul _
  simp only [quadrupoleDensity, Finset.sum_smul]
  rw [integral_finset_sum _ (fun patch _ => weightedIntegrable patch), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro patch _
  rw [evolution.integral_patchDensity_smul inside index patch]
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have areaNonzero : Real.pi * scales.radius (index.val + 1) ^ 2 ≠ 0 := by positivity
  have coefficient : patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 =
      scales.circulation (index.val + 1) *
        (patchSign patch * (Real.pi * scales.radius (index.val + 1) ^ 2)⁻¹) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    field_simp
    <;> ring
  unfold quadrupoleExternalReceiverResidual patchAverageVelocity
  have cancellation (first second : ℂ) : first + (second - first) = second := by abel
  rw [cancellation, smul_smul, smul_smul, coefficient]
  congr 1
  ring

end EulerNonuniqueness.Paper
