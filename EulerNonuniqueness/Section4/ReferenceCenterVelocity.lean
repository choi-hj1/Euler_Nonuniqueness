import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_average_velocity_sub_const_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    {velocity : ℂ → ℂ} (integrable : IntegrableOn velocity (motion.domain time index patch))
    (constant : ℂ) {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ position ∈ motion.domain time index patch, ‖velocity position - constant‖ ≤ bound) :
    ‖patchAverageVelocity scales motion time index patch velocity - constant‖ ≤ bound := by
  let area := Real.pi * scales.radius (index.val + 1) ^ 2
  have areaPositive : 0 < area := by dsimp only [area]; positivity
  have properties := evolution.2.2.2.1 time inside index patch
  have areaEquation : (volume.restrict (motion.domain time index patch)).real univ = area := by
    rw [Measure.real, Measure.restrict_apply_univ, properties.2.2.1, ENNReal.toReal_ofReal areaPositive.le]
  have constantIntegrable : IntegrableOn (fun _ : ℂ => constant) (motion.domain time index patch) :=
    integrableOn_const.mpr (Or.inr properties.2.1.measure_lt_top)
  have identity : patchAverageVelocity scales motion time index patch velocity - constant =
      area⁻¹ • ∫ position in motion.domain time index patch, velocity position - constant := by
    rw [integral_sub integrable constantIntegrable, integral_const, areaEquation, smul_sub, smul_smul,
      inv_mul_cancel₀ areaPositive.ne', one_smul]
    rfl
  have estimate := norm_integral_le_of_norm_le
    (μ := volume.restrict (motion.domain time index patch))
    (f := fun position => velocity position - constant)
    (g := fun _ : ℂ => bound)
    (integrableOn_const.mpr (Or.inr properties.2.1.measure_lt_top)) (by
      filter_upwards [ae_restrict_mem properties.1.measurableSet] with position member
      exact pointwise position member)
  rw [integral_const, areaEquation, smul_eq_mul] at estimate
  rw [identity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr areaPositive)]
  exact (mul_le_mul_of_nonneg_left estimate (inv_pos.mpr areaPositive).le).trans_eq
    (by field_simp)

theorem FinitePatchEvolution.patch_average_velocity_internal_external
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (receiver : Fin 4) :
    patchAverageVelocity scales motion time index receiver (biotSavart (patchVorticity scales motion time)) =
      (∑ source ∈ Finset.univ.erase receiver,
        patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time index source))) +
      patchAverageVelocity scales motion time index receiver (biotSavart (externalPatchVorticity scales motion time index)) := by
  rw [evolution.patch_average_velocity_decomposition inside index receiver,
    ← quadrupole_internal_point_field scales motion time index receiver]
  unfold quadrupoleInternalPatchResidual quadrupoleExternalReceiverResidual
  rw [Finset.sum_sub_distrib]
  abel

theorem FinitePatchEvolution.patch_average_velocity_relative_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius gap : ℝ}
    {strain : ℝ≥0} (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (receiver : Fin 4) (center : ℂ)
    (radiusNonnegative : 0 ≤ radius) (gapPositive : 0 < gap)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (internalSeparated : ∀ source : Fin 4, source ≠ receiver →
      ∀ position ∈ motion.domain time index receiver,
      ∀ location ∈ motion.domain time index source, gap ≤ ‖position - location‖)
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ motion.domain time source patch, distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (strain : ℝ)) :
    ‖patchAverageVelocity scales motion time index receiver (biotSavart (patchVorticity scales motion time)) -
        biotSavart (externalPatchVorticity scales motion time index) center‖ ≤
      3 * (scales.circulation (index.val + 1) / (2 * Real.pi * gap)) + (strain : ℝ) * radius := by
  classical
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have internalBound (source : Fin 4) (member : source ∈ Finset.univ.erase receiver) :
      ‖patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time index source))‖ ≤
        scales.circulation (index.val + 1) / (2 * Real.pi * gap) := by
    have estimate := evolution.patch_average_velocity_sub_const_bound
      (bound := scales.circulation (index.val + 1) / (2 * Real.pi * gap)) inside index receiver radiusPositive
      (evolution.patch_velocity_integrableOn_patch inside index index receiver source) 0 (by positivity) (by
        intro position positionInside
        simpa only [sub_zero] using (evolution.patch_biotSavart_bounds inside amplitudePositive frequencyPositive
          ratioPositive index source gapPositive (internalSeparated source (Finset.mem_erase.mp member).1 position positionInside)
          (internalSeparated source (Finset.mem_erase.mp member).1 position positionInside)).1)
    simpa only [sub_zero] using estimate
  have sumBound : ‖∑ source ∈ Finset.univ.erase receiver,
      patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time index source))‖ ≤
      3 * (scales.circulation (index.val + 1) / (2 * Real.pi * gap)) := by
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum internalBound).trans_eq (by simp)
  have externalIntegrable : IntegrableOn (biotSavart (externalPatchVorticity scales motion time index))
      (motion.domain time index receiver) := by
    rw [funext (evolution.externalPatch_biotSavart_eq_sum inside index)]
    exact integrable_finset_sum _ fun source _ => integrable_finset_sum _ fun patch _ =>
      evolution.patch_velocity_integrableOn_patch inside index source receiver patch
  have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn inside amplitudePositive frequencyPositive
    ratioPositive index distance (Metric.closedBall center radius) positive separated strainBound
  have externalBound := evolution.patch_average_velocity_sub_const_bound inside index receiver radiusPositive
    externalIntegrable (biotSavart (externalPatchVorticity scales motion time index) center)
    (mul_nonneg strain.property radiusNonnegative) (by
      intro position member
      have estimate := lipschitz.norm_sub_le (sourceBounded receiver member) (Metric.mem_closedBall_self radiusNonnegative)
      exact estimate.trans (mul_le_mul_of_nonneg_left
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded receiver member) strain.property))
  rw [evolution.patch_average_velocity_internal_external inside index receiver, add_sub_assoc]
  exact (norm_add_le _ _).trans (add_le_add sumBound externalBound)

end EulerNonuniqueness.Paper
