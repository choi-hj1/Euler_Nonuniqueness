import EulerNonuniqueness.Section6.PaperPatchReceiverDeformation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupoleExternalReceiverResidual_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (receiver : Fin 4) (distance : Fin count → ℝ)
    (control : BoundaryCloseToCircle scales motion time index receiver deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖) :
    ‖quadrupoleExternalReceiverResidual scales motion time index receiver‖ ≤
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
  have averageIdentity :
      patchAverageVelocity scales motion time index receiver (biotSavart (externalPatchVorticity scales motion time index)) =
      ∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time source patch)) := by
    unfold patchAverageVelocity
    simp_rw [evolution.externalPatch_biotSavart_eq_sum inside index]
    have outerIntegrable (source : Fin count) : IntegrableOn (fun position => ∑ patch : Fin 4,
        biotSavart (patchDensity scales motion time source patch) position) (motion.domain time index receiver) :=
      integrable_finset_sum _ (fun patch _ => evolution.patch_velocity_integrableOn_patch inside index source receiver patch)
    rw [integral_finset_sum _ (fun source _ => outerIntegrable source)]
    simp_rw [integral_finset_sum _ (fun patch _ => evolution.patch_velocity_integrableOn_patch inside index _ receiver patch),
      Finset.smul_sum]
  unfold quadrupoleExternalReceiverResidual
  rw [averageIdentity, evolution.externalPatch_biotSavart_eq_sum inside index, ← Finset.sum_sub_distrib]
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :
      ‖patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time source patch)) -
          biotSavart (patchDensity scales motion time source patch) (patchCentroid motion time index receiver)‖ ≤
        1024 * scales.circulation (source.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * distance source ^ 3) := by
    have estimate := evolution.patch_actual_receiver_averaging_bound inside amplitudePositive frequencyPositive ratioPositive
      index source receiver patch control nonnegative small (sourceBounded source member patch)
      ((receiverSmall source member).trans (separated source member patch))
      ((sourceSmall source member).trans (separated source member patch))
    apply estimate.trans
    have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have distancePositive := positive source member
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (positive source member).le (separated source member patch) 3) Real.pi_pos.le)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ source ∈ Finset.univ.erase index,
        4096 * scales.circulation (source.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * distance source ^ 3) := by
      apply Finset.sum_le_sum
      intro source member
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun patch _ => individual source member patch)).trans_eq
        (by simp only [Fin.sum_univ_succ]; ring))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _
      ring

end EulerNonuniqueness.Paper
