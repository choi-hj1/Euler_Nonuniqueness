import EulerNonuniqueness.General.WeightedAngularMoment

noncomputable section

open MeasureTheory

namespace MeasureTheory

variable {space : Type*} [NormedAddCommGroup space] [InnerProductSpace ℝ space]
  [CompleteSpace space] [MeasureSpace space]

omit [CompleteSpace space] [MeasureSpace space] in
theorem weighted_angular_flux_expansion (vorticity : space → ℝ) (velocity : space → space)
    (center displacement position : space) :
    @inner ℝ space _ (position - center) (vorticity position • (velocity position - displacement)) =
      @inner ℝ space _ position (vorticity position • velocity position) -
        @inner ℝ space _ center (vorticity position • velocity position) -
        @inner ℝ space _ displacement (vorticity position • position) +
        @inner ℝ space _ center displacement * vorticity position := by
  simp only [smul_sub, inner_sub_right, inner_sub_left, real_inner_smul_right]
  rw [real_inner_comm position displacement]
  ring

theorem integrable_weighted_angular_flux {vorticity : space → ℝ} {velocity : space → space}
    (massIntegrable : Integrable vorticity)
    (firstIntegrable : Integrable (fun position => vorticity position • position))
    (velocityIntegrable : Integrable (fun position => vorticity position • velocity position))
    (angularIntegrable : Integrable (fun position => @inner ℝ space _ position
      (vorticity position • velocity position))) (center displacement : space) :
    Integrable (fun position => @inner ℝ space _ (position - center)
      (vorticity position • (velocity position - displacement))) := by
  simp_rw [weighted_angular_flux_expansion]
  exact ((angularIntegrable.sub (velocityIntegrable.const_inner center)).sub
    (firstIntegrable.const_inner displacement)).add (massIntegrable.const_mul _)

theorem integral_weighted_angular_flux {vorticity : space → ℝ} {velocity : space → space}
    (massIntegrable : Integrable vorticity)
    (firstIntegrable : Integrable (fun position => vorticity position • position))
    (velocityIntegrable : Integrable (fun position => vorticity position • velocity position))
    (angularIntegrable : Integrable (fun position => @inner ℝ space _ position
      (vorticity position • velocity position))) (center displacement : space) :
    (∫ position, @inner ℝ space _ (position - center)
      (vorticity position • (velocity position - displacement))) =
      (∫ position, @inner ℝ space _ position (vorticity position • velocity position)) -
        @inner ℝ space _ center (∫ position, vorticity position • velocity position) -
        @inner ℝ space _ displacement (∫ position, vorticity position • position) +
        @inner ℝ space _ center displacement * ∫ position, vorticity position := by
  simp_rw [weighted_angular_flux_expansion]
  rw [integral_add
    (f := fun position => @inner ℝ space _ position (vorticity position • velocity position) -
      @inner ℝ space _ center (vorticity position • velocity position) -
      @inner ℝ space _ displacement (vorticity position • position))
    (g := fun position => @inner ℝ space _ center displacement * vorticity position)
    ((angularIntegrable.sub (velocityIntegrable.const_inner center)).sub (firstIntegrable.const_inner displacement))
    (massIntegrable.const_mul _)]
  rw [integral_sub
    (f := fun position => @inner ℝ space _ position (vorticity position • velocity position) -
      @inner ℝ space _ center (vorticity position • velocity position))
    (g := fun position => @inner ℝ space _ displacement (vorticity position • position))
    (angularIntegrable.sub (velocityIntegrable.const_inner center)) (firstIntegrable.const_inner displacement)]
  rw [integral_sub angularIntegrable (velocityIntegrable.const_inner center),
    integral_inner velocityIntegrable, integral_inner firstIntegrable, integral_const_mul]

end MeasureTheory
