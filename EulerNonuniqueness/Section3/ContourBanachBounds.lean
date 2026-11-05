import EulerNonuniqueness.Section3.ContourBanachVelocity

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem banachContourVelocity_periodic (data : PeriodicC1HolderHalf) :
    Function.Periodic (banachContourVelocity data) (2 * Real.pi) := by
  intro label
  unfold banachContourVelocity contourVelocity
  rw [PeriodicC1HolderHalf.periodic data label]

set_option maxHeartbeats 1000000 in
theorem banachContourVelocity_norm_bound (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    ‖banachContourVelocity data label‖ ≤ (‖data‖ + 1) / 2 := by
  have window := contourVelocity_periodic_source_window
    (PeriodicC1HolderHalf.periodic data) (PeriodicHolderHalf.periodic data.val.2)
    label (-Real.pi) (label - Real.pi)
  have window_identity : banachContourVelocity data label =
      contourVelocity data.val.1 data.val.2.val.1 label (label - Real.pi) (label + Real.pi) := by
    unfold banachContourVelocity
    convert window using 1 <;> congr 1 <;> ring
  rw [window_identity]
  have ordered : label - Real.pi ≤ label + Real.pi := by linarith [Real.pi_pos]
  have phase := contourVelocity_eq_phase_integral_general
    (target := label) (lower := label - Real.pi) (upper := label + Real.pi)
    (speed := ‖data‖ + 1) (chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖)
    (show label ∈ Ioo (label - Real.pi) (label + Real.pi) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    (by positivity) (sub_pos.mpr (small.trans_le (min_le_right _ _)))
    data.val.1.continuous data.val.2.val.1.continuous
    (fun current _ => PeriodicC1HolderHalf.hasDerivAt data current)
    (fun current _ => (PeriodicC1HolderHalf.speed_bound data current).trans (by linarith))
    (fun source membership => by
      rw [norm_sub_rev (data.val.1 source) (data.val.1 label)]
      apply PeriodicC1HolderHalf.chord_bound_extended data
      rw [abs_le]
      constructor <;> linarith [membership.1, membership.2, Real.pi_pos])
    (by
      have actual := (PeriodicC1HolderHalf.periodic data (label - Real.pi)).symm
      convert actual using 1 <;> congr 1 <;> ring)
  rw [phase, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ordered,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (4 * Real.pi))]
  have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := label - Real.pi) (b := label + Real.pi)
    (f := fun source => contourChordPhase data.val.1 label source * star (data.val.2.val.1 source))
    (C := ‖data‖ + 1) (fun source _ => by
      rw [norm_mul, norm_star]
      calc
        _ ≤ 1 * ‖data.val.2.val.1 source‖ :=
          mul_le_mul_of_nonneg_right (contourChordPhase_norm_le_one _ _ _) (norm_nonneg _)
        _ ≤ ‖data‖ + 1 := by
          rw [one_mul]
          exact (PeriodicC1HolderHalf.speed_bound data source).trans (by linarith))
  have length : |label + Real.pi - (label - Real.pi)| = 2 * Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  rw [length] at estimate
  apply (mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ 1 / (4 * Real.pi))).trans_eq
  field_simp
  ring

noncomputable def boundedBanachContourVelocity (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (banachContourVelocity data)
    (banachContourVelocity_differentiable data small).continuous ((‖data‖ + 1) / 2)
    (banachContourVelocity_norm_bound data small)

end EulerNonuniqueness.Paper
