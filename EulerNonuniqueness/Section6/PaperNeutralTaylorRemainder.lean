import EulerNonuniqueness.Section6.PaperExternalTaylor
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_external_taylor_remainder_integrable
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (center : ℂ) :
    Integrable (fun position => quadrupoleDensity scales motion time index position •
      (biotSavart (externalPatchVorticity scales motion time index) position -
        biotSavart (externalPatchVorticity scales motion time index) center -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (position - center))) := by
  classical
  simp only [quadrupoleDensity, Finset.sum_smul]
  apply integrable_finset_sum
  intro receiver _
  have properties := evolution.2.2.2.1 time inside index receiver
  have field : IntegrableOn (biotSavart (externalPatchVorticity scales motion time index))
      (motion.domain time index receiver) := by
    have identity : biotSavart (externalPatchVorticity scales motion time index) =
        fun position => ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
          biotSavart (patchDensity scales motion time source patch) position :=
      funext fun position => evolution.externalPatch_biotSavart_eq_sum inside index position
    rw [identity]
    exact integrable_finset_sum _ (fun source _ => integrable_finset_sum _
      (fun patch _ => evolution.patch_velocity_integrableOn_patch inside index source receiver patch))
  have affine : IntegrableOn (fun position =>
      biotSavart (externalPatchVorticity scales motion time index) center +
      fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (position - center))
      (motion.domain time index receiver) :=
    ((continuous_const.add ((fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center).continuous.comp
      (continuous_id.sub continuous_const))).continuousOn.integrableOn_compact
        properties.2.1.isCompact_closure).mono_set subset_closure
  have weighted := ((integrable_indicator_iff properties.1.measurableSet).mpr (field.sub affine)).smul
    (patchSign receiver * scales.amplitude * scales.omega (index.val + 1) ^ 4)
  convert weighted using 1
  funext position
  by_cases member : position ∈ motion.domain time index receiver <;>
    simp [patchDensity, member, sub_add_eq_sub_sub]

theorem FinitePatchEvolution.quadrupole_external_taylor_remainder_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center : ℂ)
    (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ motion.domain time source patch, distance source ≤ ‖center - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source) :
    ‖∫ position, quadrupoleDensity scales motion time index position •
      (biotSavart (externalPatchVorticity scales motion time index) position -
        biotSavart (externalPatchVorticity scales motion time index) center -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (position - center))‖ ≤
      4 * scales.circulation (index.val + 1) *
        (∑ source ∈ Finset.univ.erase index,
          4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 := by
  classical
  let coefficient := ∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  have coefficientNonnegative : 0 ≤ coefficient := by
    apply Finset.sum_nonneg
    intro source member
    exact div_nonneg (mul_nonneg (by norm_num)
      (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (positive source member).le _))
  have bounded (position : ℂ) (nonzero : quadrupoleDensity scales motion time index position ≠ 0) :
      ‖position - center‖ ≤ radius := by
    by_cases bound : ‖position - center‖ ≤ radius
    · exact bound
    exfalso
    have zero (patch : Fin 4) : patchDensity scales motion time index patch position = 0 := by
      apply indicator_of_not_mem
      intro member
      exact bound (by simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded patch member)
    exact nonzero (by simp only [quadrupoleDensity, zero, Finset.sum_const_zero])
  have pointwise (position : ℂ) :
      ‖quadrupoleDensity scales motion time index position •
        (biotSavart (externalPatchVorticity scales motion time index) position -
          biotSavart (externalPatchVorticity scales motion time index) center -
          fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (position - center))‖ ≤
        (coefficient * radius ^ 2) * |quadrupoleDensity scales motion time index position| := by
    rw [norm_smul, Real.norm_eq_abs]
    by_cases zero : quadrupoleDensity scales motion time index position = 0
    · simp only [zero, abs_zero, zero_mul, mul_zero, le_refl]
    · have estimate := evolution.externalPatch_biotSavart_fderiv_taylor_bound inside amplitudePositive
        frequencyPositive ratioPositive index distance positive separated
        (fun source member => (mul_le_mul_of_nonneg_left (bounded position zero) (by norm_num)).trans (near source member))
      have estimate' := estimate.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (bounded position zero) 2) coefficientNonnegative)
      exact (mul_le_mul_of_nonneg_left estimate' (abs_nonneg _)).trans_eq (mul_comm _ _)
  have estimate := norm_integral_le_of_norm_le
    ((evolution.quadrupoleDensity_integrable inside index).norm.const_mul (coefficient * radius ^ 2))
    (Filter.Eventually.of_forall pointwise)
  rw [integral_const_mul] at estimate
  exact estimate.trans ((mul_le_mul_of_nonneg_left
    (evolution.quadrupoleDensity_integral_abs_le inside amplitudePositive frequencyPositive ratioPositive index)
    (mul_nonneg coefficientNonnegative (sq_nonneg radius))).trans_eq (by ring))

theorem FinitePatchEvolution.quadrupole_external_first_moment_taylor_identity
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center : ℂ) :
    (∫ position, quadrupoleDensity scales motion time index position •
        biotSavart (externalPatchVorticity scales motion time index) position) -
      fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
        ((4 * scales.circulation (index.val + 1)) • centroidAsymmetry motion time index) =
      ∫ position, quadrupoleDensity scales motion time index position •
        (biotSavart (externalPatchVorticity scales motion time index) position -
          biotSavart (externalPatchVorticity scales motion time index) center -
          fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (position - center)) := by
  let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
  let remainder := fun position => quadrupoleDensity scales motion time index position •
    (biotSavart (externalPatchVorticity scales motion time index) position -
      biotSavart (externalPatchVorticity scales motion time index) center - linear (position - center))
  have remainderIntegrable : Integrable remainder :=
    evolution.quadrupole_external_taylor_remainder_integrable inside index center
  have firstIntegrable : Integrable (fun position =>
      quadrupoleDensity scales motion time index position • (position - center)) := by
    simp only [quadrupoleDensity, Finset.sum_smul]
    exact integrable_finset_sum _ (fun patch _ => evolution.integrable_patchDensity_smul_continuous
      inside index patch (continuous_id.sub continuous_const))
  have constantIntegrable := (evolution.quadrupoleDensity_integrable inside index).smul_const
    (biotSavart (externalPatchVorticity scales motion time index) center)
  have linearIntegrable := linear.integrable_comp firstIntegrable
  have zeroMean := quadrupoleDensity_integral_zero scales motion time index
    (fun patch => (evolution.2.2.2.1 time inside index patch).1)
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.1)
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.2.1)
    amplitudePositive frequencyPositive ratioPositive
  have expansion : (fun position => quadrupoleDensity scales motion time index position •
      biotSavart (externalPatchVorticity scales motion time index) position) =
      fun position => (remainder position + quadrupoleDensity scales motion time index position •
        biotSavart (externalPatchVorticity scales motion time index) center) +
        linear (quadrupoleDensity scales motion time index position • (position - center)) := by
    funext position
    rw [linear.map_smul]
    simp only [remainder, smul_sub]
    abel
  have sumIntegrable : Integrable (fun position => remainder position +
      quadrupoleDensity scales motion time index position •
        biotSavart (externalPatchVorticity scales motion time index) center) :=
    remainderIntegrable.add constantIntegrable
  rw [expansion, integral_add sumIntegrable linearIntegrable,
    integral_add remainderIntegrable constantIntegrable, integral_smul_const, zeroMean, zero_smul,
    add_zero, linear.integral_comp_comm firstIntegrable,
    evolution.integral_quadrupoleDensity_first_moment inside amplitudePositive frequencyPositive ratioPositive index center]
  exact add_sub_cancel_right _ _

end EulerNonuniqueness.Paper
