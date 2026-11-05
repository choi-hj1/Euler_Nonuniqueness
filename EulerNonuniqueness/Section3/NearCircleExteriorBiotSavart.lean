import EulerNonuniqueness.Section3.NearCircleBoundaryBiotSavart

open Set MeasureTheory Filter

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem integral_nearCircleInterior_biotSavart_off_boundary
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (point : ℂ) (off_boundary : point ∉ frontier (nearCircleInterior data small)) :
    (∫ position in nearCircleInterior data small, biotSavartKernel (point - position)) =
      pointContourVelocity data.val.1 data.val.2.val.1 point (-Real.pi) Real.pi := by
  have separated (label : ℝ) : data.val.1 label ≠ point := by
    intro equality
    apply off_boundary
    rw [nearCircleInterior_frontier data small]
    exact ⟨label, equality⟩
  have log_continuous : Continuous (fun label => Real.log ‖data.val.1 label - point‖) :=
    (data.val.1.continuous.sub continuous_const).norm.log
      (fun label => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (separated label)))
  have log_integrable : IntervalIntegrable
      (fun label => Real.log ‖data.val.1 label - point‖ • data.val.2.val.1 label)
      volume (0 - Real.pi) (0 + Real.pi) :=
    (log_continuous.smul data.val.2.val.1.continuous).intervalIntegrable _ _
  have nonzero : ∀ᵐ label ∂(volume.restrict (uIoc (0 - Real.pi) (0 + Real.pi))),
      data.val.1 label ≠ point := Eventually.of_forall separated
  have identity := integral_nearCircleInterior_biotSavart_window_of_log_integrable data small point 0
    nonzero log_integrable
  simpa only [zero_sub, zero_add, pointContourVelocity, one_div] using identity

theorem integral_nearCircleInterior_biotSavart_all_points
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) :
    (∫ position in nearCircleInterior data small, biotSavartKernel (point - position)) =
      pointContourVelocity data.val.1 data.val.2.val.1 point (-Real.pi) Real.pi := by
  by_cases on_boundary : point ∈ frontier (nearCircleInterior data small)
  · rw [nearCircleInterior_frontier data small] at on_boundary
    obtain ⟨target, rfl⟩ := on_boundary
    rw [integral_nearCircleInterior_biotSavart_boundary data small chord_small,
      pointContourVelocity_on_curve]
  · exact integral_nearCircleInterior_biotSavart_off_boundary data small point on_boundary

end

end EulerNonuniqueness.Paper
