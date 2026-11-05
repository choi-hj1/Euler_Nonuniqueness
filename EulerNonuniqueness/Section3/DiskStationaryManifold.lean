import EulerNonuniqueness.Section3.DiskStationaryChart
import EulerNonuniqueness.Section3.ScaledDiskEquilibria

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem diskNeutralCLM_material_constant (radius : ℝ) (angular : PeriodicC1HolderHalf)
    (angular_real : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskNeutralCLM (diskMaterialPerturbation (c1Constant (radius : ℂ)) angular) = angular := by
  have radial_real : ∀ label, star ((c1Constant (radius : ℂ)).val.1 label) =
      (c1Constant (radius : ℂ)).val.1 label := by
    intro label
    change star (radius : ℂ) = (radius : ℂ)
    exact Complex.conj_ofReal radius
  rw [diskNeutralCLM_apply, diskAngularCLM_materialPerturbation _ _ radial_real angular_real,
    diskRadialPart_materialPerturbation _ _ radial_real angular_real, periodicHilbertC1_constant, add_zero]

theorem diskStationaryChart_material_constant (radius : ℝ) (angular : PeriodicC1HolderHalf)
    (angular_real : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskStationaryChart (diskMaterialPerturbation (c1Constant (radius : ℂ)) angular) =
      ((1 + radius : ℝ) : ℂ) • diskRelabelCurve angular 1 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [diskStationaryChart_value, diskNeutralCLM_material_constant radius angular angular_real]
  change Complex.exp (Complex.I * angular.val.1 label) *
    (standardCircle label + standardCircle label * ((radius : ℂ) + Complex.I * angular.val.1 label) -
      Complex.I * angular.val.1 label * standardCircle label) =
    ((1 + radius : ℝ) : ℂ) * (diskRelabelCurve angular 1).val.1 label
  rw [diskRelabelCurve_value]
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_add]
  ring

theorem diskStationaryChart_material_constant_stationary (radius : ℝ) (angular : PeriodicC1HolderHalf)
    (angular_real : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (radius_nonzero : 1 + radius ≠ 0)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (chart_small : ‖diskStationaryChart (diskMaterialPerturbation (c1Constant (radius : ℂ)) angular) -
      standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (diskStationaryChart (diskMaterialPerturbation (c1Constant (radius : ℂ)) angular)) =
      (Complex.I / 2) • diskStationaryChart (diskMaterialPerturbation (c1Constant (radius : ℂ)) angular) := by
  rw [diskStationaryChart_material_constant radius angular angular_real] at chart_small ⊢
  exact extendedContourVelocity_scaled_parameterized_disk (diskRelabelCurve angular 1)
    ((1 + radius : ℝ) : ℂ) (by exact_mod_cast radius_nonzero) small chord_small
    (diskRelabelCurve_unit_norm angular angular_real 1) chart_small

end

end EulerNonuniqueness.Paper
