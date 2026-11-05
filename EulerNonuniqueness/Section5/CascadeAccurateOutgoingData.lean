import EulerNonuniqueness.Section5.CascadeFinitePassagePhysicalGap
import EulerNonuniqueness.Section6.CenteredPointProfileError
import EulerNonuniqueness.Section6.PhysicalOutgoingData
import EulerNonuniqueness.Section6.NegativeLabelBridge
import EulerNonuniqueness.Section7.PaperDipoleCoordinates

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem cascadeNormalizedPointPositions_outgoing_data_with_error {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (index : Fin count) (start time : ℝ)
    {positive negative direction rotation : ℂ} {error : ℝ}
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 64)
    (rotationNorm : ‖rotation‖ = 1) (directionNorm : ‖direction‖ = 1)
    (distanceLarge : 512 ≤ ‖positive - negative‖)
    (separationClose : ‖positive + negative - direction‖ ≤ error / 2)
    (outgoing : (7 / 8 : ℝ) * ‖positive - negative‖ ≤
      (Complex.I * star direction * (positive - negative)).re)
    (close : ‖cascadeNormalizedPointPositions scales motion index start rotation time -
      centrallySymmetricFourPoint positive negative‖ ≤ error / 4) :
    let physicalTime := start + time / scales.omega (index.val + 1)
    let physicalDirection := rotation * direction
    ‖firstDipoleSeparation motion physicalTime index - (scales.length (index.val + 1) : ℂ) * physicalDirection‖ ≤
      error * scales.length (index.val + 1) ∧
    ‖secondDipoleSeparation motion physicalTime index - (scales.length (index.val + 1) : ℂ) * (-physicalDirection)‖ ≤
      error * scales.length (index.val + 1) ∧
    (3 / 4 : ℝ) * scales.length (index.val + 1) * ‖positive - negative‖ ≤
      (Complex.I * star physicalDirection * (firstDipoleCenter motion physicalTime index -
        secondDipoleCenter motion physicalTime index)).re ∧
    ‖firstDipoleCenter motion physicalTime index - secondDipoleCenter motion physicalTime index‖ ≤
      (5 / 4 : ℝ) * scales.length (index.val + 1) * ‖positive - negative‖ := by
  let positions : FourPointConfiguration := fun patch =>
    patchCentroid motion (start + time / scales.omega (index.val + 1)) index patch
  let reference := centrallySymmetricFourPoint positive negative
  have profile := centered_point_profile_error positions reference (scales.length_pos (index.val + 1)) rotationNorm
  have physicalClose : ‖positions - (fun target => fourPointArithmeticCenter positions +
      (scales.length (index.val + 1) : ℂ) * rotation * reference target)‖ ≤
      error * scales.length (index.val + 1) / 4 := by
    rw [profile]
    have scaled := mul_le_mul_of_nonneg_left close (scales.length_pos (index.val + 1)).le
    change scales.length (index.val + 1) * ‖(fun target =>
      ((scales.length (index.val + 1) : ℂ) * rotation)⁻¹ * fourPointCenterProjection positions target) - reference‖ ≤ _ at scaled
    exact scaled.trans_eq (by ring)
  have permutedIdentity : relabelNegativePoints (fun target => fourPointArithmeticCenter positions +
      (scales.length (index.val + 1) : ℂ) * rotation * reference target) =
      fun target => fourPointArithmeticCenter positions + (scales.length (index.val + 1) : ℂ) * rotation *
        centrallySymmetricFourPoint positive (-negative) target := by
    have permuted := relabelNegativePoints_central positive negative
    funext target
    exact congrArg (fun value => fourPointArithmeticCenter positions +
      (scales.length (index.val + 1) : ℂ) * rotation * value) (congrFun permuted target)
  have permutedClose := physicalClose
  rw [← relabelNegativePoints_distance positions
    (fun target => fourPointArithmeticCenter positions + (scales.length (index.val + 1) : ℂ) * rotation * reference target),
    permutedIdentity] at permutedClose
  have actual := physical_outgoing_initial_data (scales.length_pos (index.val + 1))
    errorNonnegative errorSmall
    directionNorm rotationNorm distanceLarge separationClose outgoing permutedClose
  simpa [firstDipoleSeparation, secondDipoleSeparation, firstDipoleCenter, secondDipoleCenter,
    relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def, positions] using actual

end EulerNonuniqueness.Paper

