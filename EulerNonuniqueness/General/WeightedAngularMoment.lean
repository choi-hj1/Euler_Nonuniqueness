import Mathlib

noncomputable section

open MeasureTheory

namespace MeasureTheory

variable {space : Type*} [NormedAddCommGroup space] [InnerProductSpace ℝ space]
  [CompleteSpace space] [MeasureSpace space]

omit [CompleteSpace space] in
theorem integrable_weighted_norm_sub_sq {vorticity : space → ℝ}
    (massIntegrable : Integrable vorticity)
    (firstIntegrable : Integrable (fun position => vorticity position • position))
    (secondIntegrable : Integrable (fun position => vorticity position * ‖position‖ ^ 2))
    (center : space) : Integrable (fun position => vorticity position * ‖position - center‖ ^ 2) := by
  have identity : (fun position => vorticity position * ‖position - center‖ ^ 2) =
      fun position => vorticity position * ‖position‖ ^ 2 -
        2 * @inner ℝ space _ center (vorticity position • position) + ‖center‖ ^ 2 * vorticity position := by
    funext position
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm position center]
    ring
  rw [identity]
  exact (secondIntegrable.sub ((firstIntegrable.const_inner center).const_mul 2)).add
    (massIntegrable.const_mul _)

theorem integral_weighted_norm_sub_sq {vorticity : space → ℝ}
    (massIntegrable : Integrable vorticity)
    (firstIntegrable : Integrable (fun position => vorticity position • position))
    (secondIntegrable : Integrable (fun position => vorticity position * ‖position‖ ^ 2))
    (center : space) :
    (∫ position, vorticity position * ‖position - center‖ ^ 2) =
      (∫ position, vorticity position * ‖position‖ ^ 2) -
        2 * @inner ℝ space _ center (∫ position, vorticity position • position) +
        ‖center‖ ^ 2 * ∫ position, vorticity position := by
  have identity : (fun position => vorticity position * ‖position - center‖ ^ 2) =
      fun position => vorticity position * ‖position‖ ^ 2 -
        2 * @inner ℝ space _ center (vorticity position • position) + ‖center‖ ^ 2 * vorticity position := by
    funext position
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm position center]
    ring
  rw [identity]
  rw [integral_add (f := fun position => vorticity position * ‖position‖ ^ 2 -
      2 * @inner ℝ space _ center (vorticity position • position))
    (g := fun position => ‖center‖ ^ 2 * vorticity position)
    (secondIntegrable.sub ((firstIntegrable.const_inner center).const_mul 2)) (massIntegrable.const_mul _),
    integral_sub (f := fun position => vorticity position * ‖position‖ ^ 2)
      (g := fun position => 2 * @inner ℝ space _ center (vorticity position • position))
      secondIntegrable ((firstIntegrable.const_inner center).const_mul 2),
    integral_const_mul, integral_const_mul, integral_inner firstIntegrable]

theorem hasDerivAt_weighted_angular_moment
    {vorticity : ℝ → space → ℝ} {center : ℝ → space}
    {time massDerivative secondDerivative : ℝ} {firstDerivative centerDerivative : space}
    (massIntegrable : ∀ parameter, Integrable (vorticity parameter))
    (firstIntegrable : ∀ parameter, Integrable (fun position => vorticity parameter position • position))
    (secondIntegrable : ∀ parameter, Integrable (fun position => vorticity parameter position * ‖position‖ ^ 2))
    (massEquation : HasDerivAt (fun parameter => ∫ position, vorticity parameter position) massDerivative time)
    (firstEquation : HasDerivAt (fun parameter => ∫ position, vorticity parameter position • position) firstDerivative time)
    (secondEquation : HasDerivAt (fun parameter => ∫ position, vorticity parameter position * ‖position‖ ^ 2) secondDerivative time)
    (centerEquation : HasDerivAt center centerDerivative time) :
    HasDerivAt (fun parameter => ∫ position, vorticity parameter position * ‖position - center parameter‖ ^ 2)
      (secondDerivative - 2 *
        (@inner ℝ space _ centerDerivative (∫ position, vorticity time position • position) +
          @inner ℝ space _ (center time) firstDerivative) +
        (2 * @inner ℝ space _ (center time) centerDerivative) * (∫ position, vorticity time position) +
        ‖center time‖ ^ 2 * massDerivative) time := by
  have identity : (fun parameter => ∫ position, vorticity parameter position * ‖position - center parameter‖ ^ 2) =
      fun parameter => (∫ position, vorticity parameter position * ‖position‖ ^ 2) -
        2 * @inner ℝ space _ (center parameter) (∫ position, vorticity parameter position • position) +
        ‖center parameter‖ ^ 2 * ∫ position, vorticity parameter position := by
    funext parameter
    exact integral_weighted_norm_sub_sq (massIntegrable parameter) (firstIntegrable parameter)
      (secondIntegrable parameter) (center parameter)
  rw [identity]
  convert (secondEquation.sub ((centerEquation.inner ℝ firstEquation).const_mul 2)).add
    (centerEquation.norm_sq.mul massEquation) using 1
  ring

end MeasureTheory
