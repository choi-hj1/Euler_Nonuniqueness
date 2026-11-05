import EulerNonuniqueness.Section3.MovingPaperBoundaryControl
import EulerNonuniqueness.Section3.HolderRealPaperBound
import EulerNonuniqueness.Section3.StationaryRelabelCurve

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem diskRelabelCurve_one_value_as_phase (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) (angle : ℝ) :
    (diskRelabelCurve angular 1).val.1 angle = Complex.exp (Complex.I * (angle + (angular.val.1 angle).re : ℝ)) := by
  have imaginaryZero : (angular.val.1 angle).im = 0 := by
    have identity := congrArg Complex.im (realValues angle)
    simp only [Complex.star_def, Complex.conj_im] at identity
    linarith
  have realValue : angular.val.1 angle = ((angular.val.1 angle).re : ℂ) := by
    apply Complex.ext <;> simp [imaginaryZero]
  rw [diskRelabelCurve_value, Complex.ofReal_one, one_mul, standardCircle, ← Complex.exp_add, realValue]
  simp only [Complex.ofReal_re]
  congr 1
  push_cast
  ring

namespace FiniteMovingPatchFamily

variable {count : ℕ}

theorem boundaryCloseToCircle_of_relabel_defect (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (time : ℝ) (index : Fin count) (patch : Fin 4)
    (radiusIdentity : (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1))
    (centerIdentity : (family.patch (finProdFinEquiv (index, patch))).center time =
      Paper.patchCentroid family.patchMotion time index patch)
    (phaseIdentity : (family.patch (finProdFinEquiv (index, patch))).phase time =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2)
    (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (angularSmall : 3 * ‖angular‖ ≤ 1 / 8)
    {bound : ℝ} (defectBound :
      3 * ‖(family.patch (finProdFinEquiv (index, patch))).shape time - diskRelabelCurve angular 1‖ ≤ bound) :
    BoundaryCloseToCircle scales family.patchMotion time index patch bound := by
  refine ⟨fun angle => (angular.val.1 angle).re, ?_,
    (PeriodicC1HolderHalf.real_hasC1HalfBound angular).mono angularSmall, ?_⟩
  · intro angle
    exact congrArg Complex.re (PeriodicC1HolderHalf.periodic angular angle)
  · have control := (PeriodicC1HolderHalf.hasC1HalfBound
      ((family.patch (finProdFinEquiv (index, patch))).shape time - diskRelabelCurve angular 1)).mono defectBound
    convert control using 1
    funext angle
    rw [family.normalizedBoundary_eq_shape scales time index patch radiusIdentity centerIdentity phaseIdentity]
    change _ - Complex.exp (Complex.I * (angle + (angular.val.1 angle).re : ℝ)) =
      _ - (diskRelabelCurve angular 1).val.1 angle
    rw [diskRelabelCurve_one_value_as_phase angular realValues]

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
