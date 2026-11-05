import Mathlib

noncomputable section

open MeasureTheory

namespace MeasureTheory

set_option maxHeartbeats 1000000 in
theorem integral_norm_sub_centroid_eq
    {space : Type*} [NormedAddCommGroup space] [InnerProductSpace ℝ space]
    [CompleteSpace space] [MeasureSpace space] {domain : Set space}
    (firstIntegrable : IntegrableOn (fun position : space => position) domain)
    {center centroid : space}
    (squareIntegrable : IntegrableOn (fun position => ‖position - centroid‖ ^ 2) domain)
    (finite : volume domain < ⊤)
    (centroidMoment : (∫ position in domain, position - centroid) = 0) :
    (∫ position in domain, ‖position - centroid‖ ^ 2) =
      (∫ position in domain, ‖position - center‖ ^ 2) - volume.real domain * ‖centroid - center‖ ^ 2 := by
  have constantIntegrable : IntegrableOn (fun _ : space => centroid) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have centeredIntegrable : IntegrableOn (fun position => position - centroid) domain :=
    firstIntegrable.sub constantIntegrable
  have crossIntegrable : IntegrableOn
      (fun position => (2 : ℝ) * @inner ℝ space _ (centroid - center) (position - centroid)) domain :=
    (centeredIntegrable.const_inner (centroid - center)).const_mul 2
  have squareConstantIntegrable : IntegrableOn (fun _ : space => ‖centroid - center‖ ^ 2) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have sumIntegrable : IntegrableOn (fun position : space => ‖position - centroid‖ ^ 2 +
      (2 : ℝ) * @inner ℝ space _ (centroid - center) (position - centroid)) domain :=
    squareIntegrable.add crossIntegrable
  have crossZero : (∫ position in domain, 2 * @inner ℝ space _ (centroid - center) (position - centroid)) = 0 := by
    rw [integral_const_mul, integral_inner centeredIntegrable, centroidMoment, inner_zero_right, mul_zero]
  have constantIntegral : (∫ _position : space in domain, ‖centroid - center‖ ^ 2) =
      volume.real domain * ‖centroid - center‖ ^ 2 := by
    simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] using
      integral_const (μ := volume.restrict domain) (‖centroid - center‖ ^ 2)
  have identity :
      (∫ position in domain, ‖position - center‖ ^ 2) =
        (∫ position in domain, ‖position - centroid‖ ^ 2) + volume.real domain * ‖centroid - center‖ ^ 2 := by
    calc
      _ = ∫ position in domain, ‖position - centroid‖ ^ 2 +
          2 * @inner ℝ space _ (centroid - center) (position - centroid) + ‖centroid - center‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun position => by
          dsimp only
          rw [show position - center = (position - centroid) + (centroid - center) by abel,
            norm_add_sq_real, real_inner_comm]
      _ = (∫ position in domain, ‖position - centroid‖ ^ 2 +
          2 * @inner ℝ space _ (centroid - center) (position - centroid)) +
          (∫ _position : space in domain, ‖centroid - center‖ ^ 2) :=
        integral_add (μ := volume.restrict domain)
          (f := fun position : space => ‖position - centroid‖ ^ 2 +
            (2 : ℝ) * @inner ℝ space _ (centroid - center) (position - centroid))
          (g := fun _ : space => ‖centroid - center‖ ^ 2) sumIntegrable squareConstantIntegrable
      _ = ((∫ position in domain, ‖position - centroid‖ ^ 2) +
          (∫ position in domain, 2 * @inner ℝ space _ (centroid - center) (position - centroid))) +
          (∫ _position : space in domain, ‖centroid - center‖ ^ 2) :=
        congrArg (fun value : ℝ => value + (∫ _position : space in domain, ‖centroid - center‖ ^ 2))
          (integral_add squareIntegrable crossIntegrable)
      _ = _ := by
        rw [crossZero, constantIntegral, add_zero]
  linarith

end MeasureTheory
