import EulerNonuniqueness.Section6.PaperSignedSourceDirectTail
import EulerNonuniqueness.Section6.SeparatingStrain

noncomputable section

namespace EulerNonuniqueness.Section6

theorem rhombusConstantMomentInput_add (positive : ℝ → ℂ) (first second displacement : ℂ) (time : ℝ) :
    rhombusConstantMomentInput positive (first + second) displacement time =
      rhombusConstantMomentInput positive first displacement time +
        rhombusConstantMomentInput positive second displacement time := by
  unfold rhombusConstantMomentInput
  dsimp only
  rw [mul_add, add_div, star_add, mul_add, add_mul, add_mul, pointShapeForcing_add]
  rfl

theorem retained_moment_model_input_eq_packet (initialMoment displacement : ℂ)
    (receiverRadius receiverFrequency circulation receiverPhase outgoingPhase time : ℝ)
    (displacementNonzero : displacement ≠ 0) :
    let positive := fun elapsed => (receiverRadius : ℂ) *
      Complex.exp (Complex.I * (receiverPhase - receiverFrequency * elapsed : ℝ))
    rhombusConstantMomentInput positive
        (initialMoment + separatingLeadingMoment circulation outgoingPhase time) displacement time =
      rotatingRhombusGrowingStrainInput receiverRadius receiverFrequency circulation ‖displacement‖
          (Complex.arg displacement) receiverPhase outgoingPhase time +
        rhombusConstantMomentInput positive initialMoment displacement time := by
  dsimp only
  rw [rhombusConstantMomentInput_add]
  have strain := leadingSourceStrain_eq_moment circulation outgoingPhase time displacementNonzero
  have normalized :
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
        star (3 * separatingLeadingMoment circulation outgoingPhase time / displacement ^ 4) =
      leadingSourceStrain circulation ‖displacement‖ (Complex.arg displacement) outgoingPhase time := by
    rw [strain]
    simp only [star_div₀, star_mul, star_pow, map_ofNat]
    push_cast
    norm_num
    ring
  unfold rhombusConstantMomentInput rotatingRhombusGrowingStrainInput
  rw [normalized]
  exact add_comm _ _

end EulerNonuniqueness.Section6
