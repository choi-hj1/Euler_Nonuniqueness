import EulerNonuniqueness.General.WeightedAngularFlux

noncomputable section

open MeasureTheory

namespace MeasureTheory

variable {space : Type*} [NormedAddCommGroup space] [InnerProductSpace ℝ space]
  [CompleteSpace space] [MeasureSpace space] [BorelSpace space] [SecondCountableTopology space]

theorem abs_integral_weighted_angular_flux_le {vorticity : space → ℝ} {velocity : space → space}
    (massIntegrable : Integrable vorticity) (center displacement : space)
    (firstIntegrable : Integrable (fun position => vorticity position • (position - center)))
    (secondIntegrable : Integrable (fun position => |vorticity position| * ‖position - center‖ ^ 2))
    (velocityContinuous : Continuous velocity) {strain : ℝ} (nonnegative : 0 ≤ strain)
    (lipschitz : ∀ position ∈ Function.support vorticity,
      ‖velocity position - velocity center‖ ≤ strain * ‖position - center‖) :
    |∫ position, @inner ℝ space _ (position - center) (vorticity position • (velocity position - displacement))| ≤
      ‖∫ position, vorticity position • (position - center)‖ * ‖velocity center - displacement‖ +
        strain * ∫ position, |vorticity position| * ‖position - center‖ ^ 2 := by
  let oscillation : space → ℝ := fun position => @inner ℝ space _ (position - center)
    (vorticity position • (velocity position - velocity center))
  have bound (position : space) : ‖oscillation position‖ ≤ strain * (|vorticity position| * ‖position - center‖ ^ 2) := by
    by_cases zero : vorticity position = 0
    · simp only [oscillation, zero, zero_smul, inner_zero_right, norm_zero, abs_zero, zero_mul, mul_zero]
      exact le_rfl
    have close := lipschitz position zero
    calc
      ‖oscillation position‖ ≤ ‖position - center‖ * ‖vorticity position • (velocity position - velocity center)‖ :=
        norm_inner_le_norm _ _
      _ = ‖position - center‖ * (|vorticity position| * ‖velocity position - velocity center‖) := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖position - center‖ * (|vorticity position| * (strain * ‖position - center‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left close (abs_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have oscillationMeasurable : AEStronglyMeasurable oscillation :=
    ((continuous_id.sub continuous_const).aestronglyMeasurable).inner
      (massIntegrable.aestronglyMeasurable.smul (velocityContinuous.sub continuous_const).aestronglyMeasurable)
  have oscillationIntegrable : Integrable oscillation :=
    (secondIntegrable.const_mul strain).mono' oscillationMeasurable (Filter.Eventually.of_forall bound)
  have oscillationBound : |∫ position, oscillation position| ≤
      strain * ∫ position, |vorticity position| * ‖position - center‖ ^ 2 := by
    have estimate := norm_integral_le_of_norm_le (secondIntegrable.const_mul strain) (Filter.Eventually.of_forall bound)
    simpa only [Real.norm_eq_abs, integral_const_mul] using estimate
  have decomposition (position : space) :
      @inner ℝ space _ (position - center) (vorticity position • (velocity position - displacement)) =
      @inner ℝ space _ (velocity center - displacement) (vorticity position • (position - center)) + oscillation position := by
    dsimp only [oscillation]
    have split : velocity position - displacement =
        (velocity center - displacement) + (velocity position - velocity center) := by abel
    rw [split, smul_add, inner_add_right]
    congr 1
    simp only [real_inner_smul_right]
    rw [real_inner_comm (position - center) (velocity center - displacement)]
  simp_rw [decomposition]
  rw [integral_add (firstIntegrable.const_inner _) oscillationIntegrable, integral_inner firstIntegrable]
  apply (abs_add _ _).trans
  exact add_le_add ((abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)) oscillationBound

end MeasureTheory
