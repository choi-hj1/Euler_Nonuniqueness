import EulerNonuniqueness.Section3.DiskContourGenerator
import EulerNonuniqueness.Section3.DiskGroupOperators

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance materialCoordinatesC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def diskMaterialPerturbation (radial angular : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Product standardCircleBanach (radial + Complex.I • angular)

theorem diskRelativeC1_materialPerturbation (radial angular : PeriodicC1HolderHalf) :
    diskRelativeC1 (diskMaterialPerturbation radial angular) = radial + Complex.I • angular := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change star (standardCircle label) *
    (standardCircle label * (radial.val.1 label + Complex.I * angular.val.1 label)) =
      radial.val.1 label + Complex.I * angular.val.1 label
  rw [standardCircle_star_eq_inv]
  have nonzero : standardCircle label ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  field_simp

theorem diskRadialPart_materialPerturbation (radial angular : PeriodicC1HolderHalf)
    (radial_real : ∀ label, star (radial.val.1 label) = radial.val.1 label)
    (angular_real : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskRadialPart (diskMaterialPerturbation radial angular) = radial := by
  unfold diskRadialPart
  rw [diskRelativeC1_materialPerturbation]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℝ) • (radial.val.1 label + Complex.I * angular.val.1 label +
    star (radial.val.1 label + Complex.I * angular.val.1 label)) = radial.val.1 label
  have radial_value := radial_real label
  have angular_value := angular_real label
  simp only [Complex.star_def] at radial_value angular_value
  simp only [Complex.real_smul, Complex.star_def, map_add, map_mul, Complex.conj_I]
  rw [radial_value, angular_value]
  push_cast
  ring

theorem disk_material_generator_intertwines (radial angular : PeriodicC1HolderHalf)
    (radial_real : ∀ label, star (radial.val.1 label) = radial.val.1 label)
    (angular_real : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    fderiv ℝ extendedContourVelocity standardCircleBanach (diskMaterialPerturbation radial angular) -
      (Complex.I / 2) • diskMaterialPerturbation radial angular =
      diskMaterialPerturbation (diskLinearGenerator (radial, angular)).1 (diskLinearGenerator (radial, angular)).2 := by
  rw [disk_contour_generator, diskRadialPart_materialPerturbation radial angular radial_real angular_real,
    diskLinearGenerator_apply]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label *
      (-(1 / 2 : ℝ) • (periodicHilbertC1 radial).val.1 label - (Complex.I / 2) *
        (radial.val.1 label - (periodicMeanProjectionCCLM radial).val.1 label)) =
    standardCircle label *
      ((-1 / 2 : ℝ) • (periodicHilbertC1 radial).val.1 label + Complex.I *
        ((-1 / 2 : ℝ) • (radial.val.1 label - (periodicMeanProjectionCCLM radial).val.1 label)))
  simp only [Complex.real_smul]
  push_cast
  ring

end

end EulerNonuniqueness.Paper
