import EulerNonuniqueness.Section6.VorticitySelfInteraction

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

def complexQuadraticKernel (position : ℂ) : ℂ := position * biotSavartKernel position

theorem complexQuadraticKernel_norm (position : ℂ) :
    ‖complexQuadraticKernel position‖ ≤ 1 / (2 * Real.pi) := by
  rw [complexQuadraticKernel, norm_mul, norm_biotSavartKernel]
  by_cases zero : position = 0
  · simp [zero, Real.pi_pos.le]
  · have positive : 0 < ‖position‖ := norm_pos_iff.mpr zero
    exact le_of_eq (by field_simp; ring)

def complexQuadraticPair (first second : Vorticity) (pair : ℂ × ℂ) : ℂ :=
  first pair.1 • (second pair.2 • complexQuadraticKernel (pair.1 - pair.2))

theorem integrable_complexQuadraticPair {first second : Vorticity}
    (firstIntegrable : Integrable first) (secondIntegrable : Integrable second) :
    Integrable (complexQuadraticPair first second) (volume.prod volume) := by
  have product := firstIntegrable.norm.mul_prod secondIntegrable.norm
  apply (product.const_mul (1 / (2 * Real.pi))).mono'
    (firstIntegrable.aestronglyMeasurable.fst.smul
      (secondIntegrable.aestronglyMeasurable.snd.smul
        (((measurable_fst.sub measurable_snd).mul
          (measurable_biotSavartKernel.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable)))
  exact Filter.Eventually.of_forall fun pair => by
    change ‖first pair.1 • (second pair.2 • complexQuadraticKernel (pair.1 - pair.2))‖ ≤ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have estimate := mul_le_mul_of_nonneg_left
      (complexQuadraticKernel_norm (pair.1 - pair.2))
      (mul_nonneg (abs_nonneg (first pair.1)) (abs_nonneg (second pair.2)))
    simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using estimate

theorem integral_complexQuadraticPair_norm {first second : Vorticity}
    (firstIntegrable : Integrable first) (secondIntegrable : Integrable second) :
    ‖∫ pair : ℂ × ℂ, complexQuadraticPair first second pair ∂(volume.prod volume)‖ ≤
      (1 / (2 * Real.pi)) * (∫ position, ‖first position‖) * (∫ position, ‖second position‖) := by
  have estimate := norm_integral_le_of_norm_le
    (μ := volume.prod volume) (f := complexQuadraticPair first second)
    (((firstIntegrable.norm.mul_prod secondIntegrable.norm).const_mul (1 / (2 * Real.pi))))
    (Filter.Eventually.of_forall fun pair => by
      dsimp only [complexQuadraticPair]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have control := mul_le_mul_of_nonneg_left
        (complexQuadraticKernel_norm (pair.1 - pair.2))
        (mul_nonneg (abs_nonneg (first pair.1)) (abs_nonneg (second pair.2)))
      simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using control)
  rw [integral_const_mul] at estimate
  rw [integral_prod_mul (fun position : ℂ => ‖first position‖)
    (fun position : ℂ => ‖second position‖)] at estimate
  simpa only [mul_assoc] using estimate

theorem integral_complexQuadraticPair_difference_bound {first second : Vorticity}
    (firstIntegrable : Integrable first) (secondIntegrable : Integrable second) :
    ‖(∫ pair : ℂ × ℂ, complexQuadraticPair first first pair ∂(volume.prod volume)) -
        (∫ pair : ℂ × ℂ, complexQuadraticPair second second pair ∂(volume.prod volume))‖ ≤
      (1 / (2 * Real.pi)) * (∫ position, ‖first position - second position‖) *
        ((∫ position, ‖first position‖) + (∫ position, ‖second position‖)) := by
  have identity (pair : ℂ × ℂ) :
      complexQuadraticPair first first pair - complexQuadraticPair second second pair =
        complexQuadraticPair (first - second) first pair +
          complexQuadraticPair second (first - second) pair := by
    simp only [complexQuadraticPair, Pi.sub_apply, sub_smul, smul_sub]
    abel
  rw [← integral_sub (integrable_complexQuadraticPair firstIntegrable firstIntegrable)
    (integrable_complexQuadraticPair secondIntegrable secondIntegrable)]
  simp_rw [identity]
  rw [integral_add (integrable_complexQuadraticPair (firstIntegrable.sub secondIntegrable) firstIntegrable)
    (integrable_complexQuadraticPair secondIntegrable (firstIntegrable.sub secondIntegrable))]
  apply (norm_add_le _ _).trans
  apply (add_le_add
    (integral_complexQuadraticPair_norm (firstIntegrable.sub secondIntegrable) firstIntegrable)
    (integral_complexQuadraticPair_norm secondIntegrable (firstIntegrable.sub secondIntegrable))).trans_eq
  simp only [Pi.sub_apply]
  ring

end EulerNonuniqueness.Section6
