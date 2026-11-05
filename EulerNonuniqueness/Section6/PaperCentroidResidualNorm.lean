import EulerNonuniqueness.Section6.PaperCentroidDeformationResidual

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_deformation_residual_norm_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 8 * scales.radius (index.val + 1) ≤ gap)
    (internalSeparated : ∀ receiver source : Fin 4, source ≠ receiver →
      gap ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time index source‖)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (separated : ∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
      distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖) :
    ‖((fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
        quadrupoleExternalReceiverResidual scales motion time index patch) : Fin 4 → ℂ)‖ ≤
      3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
  have individual (receiver : Fin 4) := evolution.quadrupoleInternalPatchResidual_bound inside
    amplitudePositive frequencyPositive ratioPositive index receiver control nonnegative small gapPositive radiusSmall
    (fun source member => internalSeparated receiver source (Finset.mem_erase.mp member).1)
  have external (receiver : Fin 4) := evolution.quadrupoleExternalReceiverResidual_bound inside
    amplitudePositive frequencyPositive ratioPositive index receiver distance (control receiver) nonnegative small
    positive sourceBounded receiverSmall sourceSmall (separated receiver)
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have sumNonnegative : 0 ≤ ∑ source ∈ Finset.univ.erase index,
      scales.circulation (source.val + 1) / distance source ^ 3 := by
    exact Finset.sum_nonneg fun source member => div_nonneg
      (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (positive source member).le _)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro receiver
  exact (norm_add_le _ _).trans (add_le_add (individual receiver) (external receiver))

end EulerNonuniqueness.Paper
