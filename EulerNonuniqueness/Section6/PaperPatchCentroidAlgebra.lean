import EulerNonuniqueness.Section6.MovingExternalPatchDerivative
import EulerNonuniqueness.Section6.PatchPointFieldIdentity

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def patchAverageVelocity {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (receiver : Fin 4) (velocity : ℂ → ℂ) : ℂ :=
  (Real.pi * scales.radius (index.val + 1) ^ 2)⁻¹ •
    ∫ position in motion.domain time index receiver, velocity position

def quadrupoleInternalPatchResidual {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (receiver : Fin 4) : ℂ :=
  ∑ source ∈ Finset.univ.erase receiver,
    (patchAverageVelocity scales motion time index receiver (biotSavart (patchDensity scales motion time index source)) -
      (patchSign source * scales.circulation (index.val + 1)) •
        biotSavartKernel (patchCentroid motion time index receiver - patchCentroid motion time index source))

def quadrupoleExternalReceiverResidual {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (receiver : Fin 4) : ℂ :=
  patchAverageVelocity scales motion time index receiver (biotSavart (externalPatchVorticity scales motion time index)) -
    biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index receiver)

theorem FinitePatchEvolution.patch_velocity_integrableOn_patch
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (receiverIndex sourceIndex : Fin count) (receiver source : Fin 4) :
    IntegrableOn (biotSavart (patchDensity scales motion time sourceIndex source))
      (motion.domain time receiverIndex receiver) := by
  have sourceProperties := evolution.2.2.2.1 time inside sourceIndex source
  have receiverProperties := evolution.2.2.2.1 time inside receiverIndex receiver
  apply Section6.integrableOn_biotSavart_of_L1_L4_finite
    (patchDensity_integrable scales motion time sourceIndex source sourceProperties.1 sourceProperties.2.1)
    _ receiverProperties.2.1.measure_lt_top
  exact memLp_indicator_const _ sourceProperties.1.measurableSet _ (Or.inr sourceProperties.2.1.measure_lt_top.ne)

theorem FinitePatchEvolution.patch_average_self_velocity_zero
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (patch : Fin 4) :
    patchAverageVelocity scales motion time index patch (biotSavart (patchDensity scales motion time index patch)) = 0 := by
  have properties := evolution.2.2.2.1 time inside index patch
  obtain ⟨radius, _, bounded⟩ := properties.2.1.exists_pos_norm_le
  have zero := Section6.integral_patch_self_interaction_density properties.1.measurableSet
    (show motion.domain time index patch ⊆ Metric.closedBall 0 radius from fun position member => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using bounded position member)
    (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
  simpa only [patchAverageVelocity, patchDensity, smul_zero] using
    congrArg (fun value : ℂ => (Real.pi * scales.radius (index.val + 1) ^ 2)⁻¹ • value) zero

theorem quadrupole_internal_point_field (scales : Scales) {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (receiver : Fin 4) :
    (∑ source ∈ Finset.univ.erase receiver, (patchSign source * scales.circulation (index.val + 1)) •
      biotSavartKernel (patchCentroid motion time index receiver - patchCentroid motion time index source)) =
      Section6.fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid motion time index patch) receiver := by
  rw [← Section6.finitePointField_eq_circulation_kernel_sum]
  have coefficient : (fun source : Fin 4 => patchSign source * scales.circulation (index.val + 1) / (2 * Real.pi)) =
      fun source => (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) * Section6.fourPointSign source := by
    funext source
    have sign : patchSign source = Section6.fourPointSign source := rfl
    rw [sign, Scales.circulation]
    field_simp [Real.pi_ne_zero]
    ring
  rw [coefficient, Section6.finitePointField_fourPoint_identity]

theorem FinitePatchEvolution.patchVorticity_biotSavart_internal_external
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (position : ℂ) :
    biotSavart (patchVorticity scales motion time) position =
      (∑ patch : Fin 4, biotSavart (patchDensity scales motion time index patch) position) +
        biotSavart (externalPatchVorticity scales motion time index) position := by
  have sumIdentity : biotSavart (patchVorticity scales motion time) position =
      ∑ source : Fin count, biotSavart (quadrupoleDensity scales motion time source) position := by
    simp only [biotSavart, patchVorticity, Finset.sum_smul]
    apply integral_finset_sum
    intro source _
    simp only [quadrupoleDensity, Finset.sum_smul]
    exact integrable_finset_sum _ (fun patch _ => evolution.patch_biotSavart_integrand_integrable inside source patch position)
  rw [sumIdentity, ← Finset.sum_erase_add Finset.univ
    (fun source => biotSavart (quadrupoleDensity scales motion time source) position) (Finset.mem_univ index),
    evolution.quadrupole_biotSavart_eq_sum_patch inside index position,
    evolution.externalPatch_biotSavart_eq_sum inside index position]
  simp_rw [evolution.quadrupole_biotSavart_eq_sum_patch inside]
  exact add_comm _ _

theorem FinitePatchEvolution.patch_average_velocity_decomposition
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) (receiver : Fin 4) :
    patchAverageVelocity scales motion time index receiver (biotSavart (patchVorticity scales motion time)) =
      Section6.fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid motion time index patch) receiver +
        biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index receiver) +
        quadrupoleInternalPatchResidual scales motion time index receiver +
        quadrupoleExternalReceiverResidual scales motion time index receiver := by
  let average := fun source : Fin 4 => patchAverageVelocity scales motion time index receiver
    (biotSavart (patchDensity scales motion time index source))
  have internalIntegrable : IntegrableOn (fun position => ∑ patch : Fin 4,
      biotSavart (patchDensity scales motion time index patch) position) (motion.domain time index receiver) :=
    integrable_finset_sum _ (fun patch _ => evolution.patch_velocity_integrableOn_patch inside index index receiver patch)
  have externalIntegrable : IntegrableOn (biotSavart (externalPatchVorticity scales motion time index))
      (motion.domain time index receiver) := by
    have identity := funext (evolution.externalPatch_biotSavart_eq_sum inside index)
    rw [identity]
    exact integrable_finset_sum _ (fun source _ => integrable_finset_sum _ (fun patch _ =>
      evolution.patch_velocity_integrableOn_patch inside index source receiver patch))
  have averageIdentity :
      patchAverageVelocity scales motion time index receiver (biotSavart (patchVorticity scales motion time)) =
      (∑ source : Fin 4, average source) +
        patchAverageVelocity scales motion time index receiver (biotSavart (externalPatchVorticity scales motion time index)) := by
    unfold patchAverageVelocity
    simp_rw [evolution.patchVorticity_biotSavart_internal_external inside index]
    rw [integral_add internalIntegrable externalIntegrable, integral_finset_sum _
      (fun patch _ => evolution.patch_velocity_integrableOn_patch inside index index receiver patch), smul_add, Finset.smul_sum]
    rfl
  have erased := Finset.sum_erase_add Finset.univ average (Finset.mem_univ receiver)
  have own : average receiver = 0 := evolution.patch_average_self_velocity_zero inside index receiver
  rw [own, add_zero] at erased
  rw [averageIdentity, ← erased, ← quadrupole_internal_point_field scales motion time index receiver]
  unfold quadrupoleInternalPatchResidual quadrupoleExternalReceiverResidual
  rw [Finset.sum_sub_distrib]
  dsimp only [average]
  abel

end EulerNonuniqueness.Paper
