import EulerNonuniqueness.Section3.ContourCentroidCircleDerivative

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidCircleRadialHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance centroidCircleRadialC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourCentroidFunctional_circle_derivative_radial (direction : PeriodicC1HolderHalf) :
    (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction =
      (1 / (Real.pi : ℂ)) * ∫ label in (-Real.pi)..Real.pi,
        standardCircle label * (diskRadialPart direction).val.1 label := by
  rw [contourCentroidFunctional_circle_derivative]
  have identity : (fun label => direction.val.1 label +
      standardCircleBanach.val.1 label ^ 2 * star (direction.val.1 label)) =
      fun label => (2 : ℂ) * (standardCircle label * (diskRadialPart direction).val.1 label) := by
    funext label
    have unit : standardCircle label * star (standardCircle label) = (1 : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, standardCircle_norm]
      norm_num
    change direction.val.1 label + standardCircle label ^ 2 * star (direction.val.1 label) =
      2 * (standardCircle label * ((1 / 2 : ℝ) •
        (star (standardCircle label) * direction.val.1 label +
          star (star (standardCircle label) * direction.val.1 label))))
    rw [star_mul, star_star, Complex.real_smul]
    push_cast
    calc
      _ = (standardCircle label * star (standardCircle label)) * direction.val.1 label +
          standardCircle label ^ 2 * star (direction.val.1 label) := by rw [unit, one_mul]
      _ = _ := by ring
  rw [identity, intervalIntegral.integral_const_mul]
  have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  <;> ring

theorem contourCentroidFunctional_circle_derivative_material (radial angular : PeriodicC1HolderHalf)
    (radialReal : ∀ label, star (radial.val.1 label) = radial.val.1 label)
    (angularReal : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    (fderiv ℝ contourCentroidFunctional standardCircleBanach) (diskMaterialPerturbation radial angular) =
      (1 / (Real.pi : ℂ)) * ∫ label in (-Real.pi)..Real.pi, standardCircle label * radial.val.1 label := by
  rw [contourCentroidFunctional_circle_derivative_radial,
    diskRadialPart_materialPerturbation radial angular radialReal angularReal]

theorem diskRadialPart_first_moment_zero_of_centroid_tangent (direction : PeriodicC1HolderHalf)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    (∫ label in (-Real.pi)..Real.pi, standardCircle label * (diskRadialPart direction).val.1 label) = 0 := by
  rw [contourCentroidFunctional_circle_derivative_radial] at centered
  exact (mul_eq_zero.mp centered).resolve_left (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

end EulerNonuniqueness.Paper
