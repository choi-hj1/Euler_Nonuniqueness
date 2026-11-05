import EulerNonuniqueness.Section8.TestSlices

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem scalarTest_uniform_bounds {test : ℝ × Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ time position,
      ‖test (time, position)‖ ≤ bound ∧ ‖timeDerivative test (time, position)‖ ≤ bound ∧
      ∀ direction, ‖spatialDerivative test (time, position) direction‖ ≤ bound * ‖direction‖ := by
  obtain ⟨valueBound, valueBounded⟩ := compact.exists_bound_of_continuous smooth.continuous
  obtain ⟨derivativeBound, derivativeBounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuous
    (smooth.continuous_fderiv (by simp))
  let bound := max (max valueBound derivativeBound) 0
  have nonnegative : 0 ≤ bound := le_max_right _ _
  have valueBounded' (point : ℝ × Plane) : ‖test point‖ ≤ bound :=
    (valueBounded point).trans ((le_max_left _ _).trans (le_max_left _ _))
  have derivativeBounded' (point : ℝ × Plane) : ‖fderiv ℝ test point‖ ≤ bound :=
    (derivativeBounded point).trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨bound, nonnegative, ?_⟩
  intro time position
  refine ⟨valueBounded' _, ?_, ?_⟩
  · have estimate := (fderiv ℝ test (time, position)).le_opNorm (1, 0)
    simpa only [timeDerivative, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one] using
      estimate.trans (by simpa using derivativeBounded' (time, position))
  · intro direction
    have estimate := (fderiv ℝ test (time, position)).le_opNorm (0, direction)
    simpa only [spatialDerivative, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg direction)] using
      estimate.trans (mul_le_mul_of_nonneg_right (derivativeBounded' _) (norm_nonneg (0, direction)))

theorem scalarTest_spatial_support {test : ℝ × Plane → ℝ} (compact : HasCompactSupport test) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ time position, position ∉ Metric.closedBall (0 : Plane) radius →
      test (time, position) = 0 ∧ timeDerivative test (time, position) = 0 ∧
      ∀ direction, spatialDerivative test (time, position) direction = 0 := by
  obtain ⟨radius, positive, bounded⟩ :=
    (compact.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  refine ⟨radius, positive, ?_⟩
  intro time position outside
  have outsideSupport : (time, position) ∉ tsupport test := by
    intro inside
    apply outside
    simpa using bounded position ⟨(time, position), inside, rfl⟩
  have testZero := image_eq_zero_of_nmem_tsupport outsideSupport
  have derivativeZero := fderiv_of_not_mem_tsupport (𝕜 := ℝ) outsideSupport
  simp only [testZero, timeDerivative, spatialDerivative, derivativeZero, ContinuousLinearMap.zero_apply,
    and_self, implies_true]

end EulerNonuniqueness
