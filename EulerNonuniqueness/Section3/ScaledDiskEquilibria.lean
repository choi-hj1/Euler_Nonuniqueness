import EulerNonuniqueness.Section3.ContourVelocityScaling
import EulerNonuniqueness.Section3.ParameterizedDiskEquilibria

namespace EulerNonuniqueness.Paper

noncomputable section

theorem extendedContourVelocity_parameterized_unit_disk (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (unit_norm : ∀ label, ‖data.val.1 label‖ = 1) :
    extendedContourVelocity data = (Complex.I / 2) • data := by
  have near : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    lt_min (small.trans (by norm_num)) chord_small
  rw [extendedContourVelocity_eq data near]
  apply PeriodicC1HolderHalf.ext_value
  intro target
  exact contourVelocity_eq_disk_rotation_of_unit_norm data small chord_small unit_norm target

theorem extendedContourVelocity_scaled_parameterized_disk (data : PeriodicC1HolderHalf)
    (scalar : ℂ) (nonzero : scalar ≠ 0)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (unit_norm : ∀ label, ‖data.val.1 label‖ = 1)
    (scaled_small : ‖scalar • data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (scalar • data) = (Complex.I / 2) • (scalar • data) := by
  rw [extendedContourVelocity_scale data scalar nonzero
    (lt_min (small.trans (by norm_num)) chord_small) scaled_small,
    extendedContourVelocity_parameterized_unit_disk data small chord_small unit_norm]
  exact smul_comm _ _ _

end

end EulerNonuniqueness.Paper
