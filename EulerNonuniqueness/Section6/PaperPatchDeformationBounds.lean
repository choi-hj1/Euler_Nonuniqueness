import EulerNonuniqueness.Section6.PaperPatchReceiverDeformation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_biotSavart_point_error_of_boundaryControl
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (patch : Fin 4) (position : ℂ)
    (control : BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (separated : 4 * scales.radius (index.val + 1) ≤ ‖position - patchCentroid motion time index patch‖) :
    ‖biotSavart (patchDensity scales motion time index patch) position -
        (patchSign patch * scales.circulation (index.val + 1)) •
          biotSavartKernel (position - patchCentroid motion time index patch)‖ ≤
      128 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * ‖position - patchCentroid motion time index patch‖ ^ 3) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have trapping := evolution.domain_radial_trapping inside index patch control nonnegative (by linarith) radiusPositive
  have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  let density := patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  have mass : density * (Real.pi * scales.radius (index.val + 1) ^ 2) =
      patchSign patch * scales.circulation (index.val + 1) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    dsimp only [density]
    ring
  have absoluteMass := evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive index patch
  rw [area] at absoluteMass
  have estimate := Section6.biotSavart_patch_relative_deformation_bound properties.1.measurableSet
    (patchCentroid motion time index patch) (patchCentroid motion time index patch) position radiusPositive
    nonnegative small trapping.1 trapping.2 area
    (evolution.patch_centroid_centered_integral_zero inside index patch) separated density
  rw [abs_mul density (Real.pi * scales.radius (index.val + 1) ^ 2),
    abs_of_pos (by positivity : 0 < Real.pi * scales.radius (index.val + 1) ^ 2), absoluteMass, mass] at estimate
  exact estimate

theorem FinitePatchEvolution.patch_pair_point_error_of_boundaryControl
    {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon time receiverDeformation sourceDeformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (receiverIndex sourceIndex : Fin count) (receiver source : Fin 4)
    (receiverControl : BoundaryCloseToCircle scales motion time receiverIndex receiver receiverDeformation)
    (sourceControl : BoundaryCloseToCircle scales motion time sourceIndex source sourceDeformation)
    (receiverNonnegative : 0 ≤ receiverDeformation) (receiverSmall : receiverDeformation ≤ 1 / 16)
    (sourceNonnegative : 0 ≤ sourceDeformation) (sourceSmall : sourceDeformation ≤ 1 / 16)
    (receiverSeparated : 8 * scales.radius (receiverIndex.val + 1) ≤
      ‖patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source‖)
    (sourceSeparated : 4 * scales.radius (sourceIndex.val + 1) ≤
      ‖patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source‖) :
    ‖patchAverageVelocity scales motion time receiverIndex receiver
        (biotSavart (patchDensity scales motion time sourceIndex source)) -
      (patchSign source * scales.circulation (sourceIndex.val + 1)) •
        biotSavartKernel (patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source)‖ ≤
      128 * scales.circulation (sourceIndex.val + 1) *
        (scales.radius (sourceIndex.val + 1) ^ 2 * sourceDeformation +
          8 * scales.radius (receiverIndex.val + 1) ^ 2 * receiverDeformation) /
        (Real.pi * ‖patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source‖ ^ 3) := by
  have sourceRadiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (sourceIndex.val + 1)
  have sourceTrapping := evolution.domain_radial_trapping inside sourceIndex source sourceControl sourceNonnegative
    (by linarith) sourceRadiusPositive
  have sourceBounded : motion.domain time sourceIndex source ⊆
      Metric.closedBall (patchCentroid motion time sourceIndex source) (2 * scales.radius (sourceIndex.val + 1)) := by
    intro position member
    have bound := sourceTrapping.2 member
    rw [Metric.mem_ball, dist_eq_norm] at bound
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    nlinarith
  have receiverEstimate := evolution.patch_actual_receiver_averaging_bound inside amplitudePositive frequencyPositive
    ratioPositive receiverIndex sourceIndex receiver source receiverControl receiverNonnegative receiverSmall
    sourceBounded receiverSeparated sourceSeparated
  have sourceEstimate := evolution.patch_biotSavart_point_error_of_boundaryControl inside amplitudePositive frequencyPositive
    ratioPositive sourceIndex source (patchCentroid motion time receiverIndex receiver) sourceControl
    sourceNonnegative sourceSmall sourceSeparated
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (biotSavart (patchDensity scales motion time sourceIndex source) (patchCentroid motion time receiverIndex receiver)) _).trans
  exact (add_le_add receiverEstimate sourceEstimate).trans_eq (by ring)

theorem FinitePatchEvolution.quadrupoleInternalPatchResidual_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (receiver : Fin 4)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 8 * scales.radius (index.val + 1) ≤ gap)
    (separated : ∀ source ∈ Finset.univ.erase receiver,
      gap ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time index source‖) :
    ‖quadrupoleInternalPatchResidual scales motion time index receiver‖ ≤
      3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) := by
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  unfold quadrupoleInternalPatchResidual
  apply (norm_sum_le _ _).trans
  have individual (source : Fin 4) (member : source ∈ Finset.univ.erase receiver) :
      ‖patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time index source)) -
        (patchSign source * scales.circulation (index.val + 1)) •
          biotSavartKernel (patchCentroid motion time index receiver - patchCentroid motion time index source)‖ ≤
      1152 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) := by
    have estimate := evolution.patch_pair_point_error_of_boundaryControl inside amplitudePositive frequencyPositive ratioPositive
      index index receiver source (control receiver) (control source) nonnegative small nonnegative small
      (radiusSmall.trans (separated source member)) (by linarith [separated source member])
    apply estimate.trans
    have numerator : 128 * scales.circulation (index.val + 1) *
        (scales.radius (index.val + 1) ^ 2 * deformation + 8 * scales.radius (index.val + 1) ^ 2 * deformation) =
        1152 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation := by ring
    rw [numerator]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gapPositive.le (separated source member) 3) Real.pi_pos.le)
  apply (Finset.sum_le_sum individual).trans_eq
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ receiver)]
  norm_num
  ring

end EulerNonuniqueness.Paper
