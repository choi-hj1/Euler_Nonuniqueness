import EulerNonuniqueness.Section3.FiniteMovingPatchMotion
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound

noncomputable section

namespace EulerNonuniqueness.Paper

theorem movingSimilarity_unrotate (center value : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) (phase : ℝ) :
    Complex.exp (-Complex.I * (phase : ℂ)) *
      ((center + radius • ((Circle.exp phase : ℂ) * value) - center) / (radius : ℂ)) = value := by
  have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr radiusPositive.ne'
  have quotient : ((radius : ℂ) * ((Circle.exp phase : ℂ) * value)) / (radius : ℂ) =
      (Circle.exp phase : ℂ) * value := by
    apply (div_eq_iff radiusNonzero).mpr
    ring
  have inverseRotation : Complex.exp (-Complex.I * (phase : ℂ)) * (Circle.exp phase : ℂ) = 1 := by
    rw [Circle.coe_exp, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  rw [add_sub_cancel_left, Complex.real_smul, quotient, ← mul_assoc, inverseRotation, one_mul]

namespace FiniteMovingPatchFamily

variable {count : ℕ}

theorem normalizedBoundary_eq_shape (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (time : ℝ) (index : Fin count) (patch : Fin 4)
    (radiusIdentity : (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1))
    (centerIdentity : (family.patch (finProdFinEquiv (index, patch))).center time =
      Paper.patchCentroid family.patchMotion time index patch)
    (phaseIdentity : (family.patch (finProdFinEquiv (index, patch))).phase time =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2) (angle : ℝ) :
    normalizedBoundary scales family.patchMotion time index patch angle =
      ((family.patch (finProdFinEquiv (index, patch))).shape time).val.1 angle := by
  unfold normalizedBoundary
  change Complex.exp (-Complex.I *
      (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2 : ℝ)) *
    (((family.patch (finProdFinEquiv (index, patch))).boundary time angle -
      Paper.patchCentroid family.patchMotion time index patch) / (scales.radius (index.val + 1) : ℂ)) = _
  rw [← centerIdentity, ← radiusIdentity, ← phaseIdentity]
  exact movingSimilarity_unrotate _ _ (family.patch (finProdFinEquiv (index, patch))).radius_positive _

theorem boundaryCloseToCircle_of_shape_norm (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (time : ℝ) (index : Fin count) (patch : Fin 4)
    (radiusIdentity : (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1))
    (centerIdentity : (family.patch (finProdFinEquiv (index, patch))).center time =
      Paper.patchCentroid family.patchMotion time index patch)
    (phaseIdentity : (family.patch (finProdFinEquiv (index, patch))).phase time =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2)
    {bound : ℝ} (normBound : 3 * ‖(family.patch (finProdFinEquiv (index, patch))).shape time - standardCircleBanach‖ ≤ bound) :
    BoundaryCloseToCircle scales family.patchMotion time index patch bound := by
  refine ⟨fun _ => 0, ?_, hasC1HalfBound_zero.mono (by norm_num), ?_⟩
  · intro angle
    rfl
  · have control := (PeriodicC1HolderHalf.hasC1HalfBound
      ((family.patch (finProdFinEquiv (index, patch))).shape time - standardCircleBanach)).mono normBound
    convert control using 1
    funext angle
    rw [family.normalizedBoundary_eq_shape scales time index patch radiusIdentity centerIdentity phaseIdentity]
    simp only [add_zero]
    change _ - Complex.exp (Complex.I * (angle : ℂ)) = _ - standardCircle angle
    rw [standardCircle]
    congr 2
    ring

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
