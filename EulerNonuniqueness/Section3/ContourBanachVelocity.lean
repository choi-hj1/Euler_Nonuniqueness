import EulerNonuniqueness.Section3.CircleBanach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem standardCircle_chord_bound_extended {target source : ℝ}
    (nearby : |source - target| ≤ 3 * Real.pi / 2) :
    (2 / (3 * Real.pi)) * |source - target| ≤ ‖standardCircle source - standardCircle target‖ := by
  have pi_pos := Real.pi_pos
  have coefficient_pos : 0 < 2 / Real.pi := by positivity
  have coefficient_identity : 2 / (3 * Real.pi) = (2 / Real.pi) / 3 := by ring
  by_cases central : |source - target| ≤ Real.pi
  · apply (mul_le_mul_of_nonneg_right (show 2 / (3 * Real.pi) ≤ 2 / Real.pi from by
        rw [coefficient_identity]; linarith) (abs_nonneg _)).trans
    exact standardCircle_chord_bound_centered central
  by_cases positive : 0 ≤ source - target
  · have distance : |source - target| = source - target := abs_of_nonneg positive
    have reduced : |source - 2 * Real.pi - target| = 2 * Real.pi - (source - target) := by
      rw [abs_of_neg (by rw [distance] at nearby; linarith)]
      ring
    have reduced_near : |source - 2 * Real.pi - target| ≤ Real.pi := by
      rw [reduced]
      rw [distance] at central
      linarith
    have same : standardCircle (source - 2 * Real.pi) = standardCircle source := by
      simpa only [sub_add_cancel] using (standardCircle_periodic (source - 2 * Real.pi)).symm
    have estimate := standardCircle_chord_bound_centered reduced_near
    rw [same] at estimate
    apply le_trans _ estimate
    rw [distance, reduced, coefficient_identity]
    rw [distance] at nearby
    have bound : (source - target) / 3 ≤ 2 * Real.pi - (source - target) := by linarith
    convert mul_le_mul_of_nonneg_left bound coefficient_pos.le using 1 <;> ring
  · have distance : |source - target| = target - source := by rw [abs_of_neg (lt_of_not_ge positive)]; ring
    have reduced : |source + 2 * Real.pi - target| = 2 * Real.pi - (target - source) := by
      rw [abs_of_pos (by rw [distance] at nearby; linarith)]
      ring
    have reduced_near : |source + 2 * Real.pi - target| ≤ Real.pi := by
      rw [reduced]
      rw [distance] at central
      linarith
    have same := standardCircle_periodic source
    have estimate := standardCircle_chord_bound_centered reduced_near
    rw [same] at estimate
    apply le_trans _ estimate
    rw [distance, reduced, coefficient_identity]
    rw [distance] at nearby
    have bound : (target - source) / 3 ≤ 2 * Real.pi - (target - source) := by linarith
    convert mul_le_mul_of_nonneg_left bound coefficient_pos.le using 1 <;> ring

theorem contourVelocity_periodic_source_window {curve tangent : ℝ → ℂ}
    (curve_periodic : Function.Periodic curve (2 * Real.pi))
    (tangent_periodic : Function.Periodic tangent (2 * Real.pi)) (target first second : ℝ) :
    contourVelocity curve tangent target first (first + 2 * Real.pi) =
      contourVelocity curve tangent target second (second + 2 * Real.pi) := by
  have periodic : Function.Periodic
      (fun source => Real.log ‖curve target - curve source‖ • tangent source) (2 * Real.pi) := by
    intro source
    dsimp only
    rw [curve_periodic source, tangent_periodic source]
  unfold contourVelocity
  rw [periodic.intervalIntegral_add_eq first second]

theorem PeriodicC1HolderHalf.chord_bound_extended (data : PeriodicC1HolderHalf)
    {target source : ℝ} (nearby : |source - target| ≤ 3 * Real.pi / 2) :
    (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) * |source - target| ≤
      ‖data.val.1 target - data.val.1 source‖ := by
  have actual := contour_chord_lower_of_derivative_close
    (show target ∈ Icc (min target source) (max target source) from ⟨min_le_left _ _, le_max_left _ _⟩)
    (show source ∈ Icc (min target source) (max target source) from ⟨min_le_right _ _, le_max_right _ _⟩)
    (fun current _ => PeriodicC1HolderHalf.hasDerivAt data current)
    (fun current _ => standardCircle_derivative current)
    (fun current _ => PeriodicC1HolderHalf.derivative_close_circle data current)
    (standardCircle_chord_bound_extended nearby)
  rwa [norm_sub_rev] at actual

noncomputable def banachContourVelocity (data : PeriodicC1HolderHalf) (label : ℝ) : ℂ :=
  contourVelocity data.val.1 data.val.2.val.1 label (-Real.pi) Real.pi

set_option maxHeartbeats 1000000 in
theorem banachContourVelocity_hasDerivAt (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    HasDerivAt (banachContourVelocity data)
      ((1 / (4 * Real.pi)) • ∫ source in Icc (label - Real.pi) (label + Real.pi),
        contourChordPhaseDerivative data.val.1 data.val.2.val.1 label source *
          star (data.val.2.val.1 source)) label := by
  have tangent_nonzero : ∀ current : ℝ, data.val.2.val.1 current ≠ 0 := by
    intro current equal
    have bound := PeriodicC1HolderHalf.derivative_close_circle data current
    rw [equal, zero_sub, norm_neg, standardCircleTangent_norm] at bound
    exact (not_le_of_gt (small.trans_le (min_le_left _ _))) bound
  have closed : data.val.1 (label - Real.pi) = data.val.1 (label + Real.pi) := by
    have actual := (PeriodicC1HolderHalf.periodic data (label - Real.pi)).symm
    convert actual using 1 <;> congr 1 <;> ring
  have actual := hasDerivAt_contourVelocity
    (target := label) (parameterRadius := Real.pi / 4)
    (lower := label - Real.pi) (upper := label + Real.pi)
    (holder := ‖data‖) (speed := ‖data‖ + 1)
    (chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖)
    (by positivity) (norm_nonneg _) (by positivity)
    (sub_pos.mpr (small.trans_le (min_le_right _ _)))
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    data.val.1.continuous data.val.2.val.1.continuous
    (fun current _ => PeriodicC1HolderHalf.hasDerivAt data current)
    (fun current _ => tangent_nonzero current)
    (fun current _ => (PeriodicC1HolderHalf.speed_bound data current).trans (by linarith))
    (fun first _ second _ => PeriodicC1HolderHalf.derivative_holder_bound data first second)
    (fun parameter parameter_mem source source_mem => by
      rw [abs_sub_comm parameter source]
      apply PeriodicC1HolderHalf.chord_bound_extended data
      rw [abs_le]
      constructor <;> linarith [parameter_mem.1, parameter_mem.2, source_mem.1, source_mem.2, Real.pi_pos]) closed
  apply actual.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro parameter
  unfold banachContourVelocity
  have identity := contourVelocity_periodic_source_window
    (PeriodicC1HolderHalf.periodic data) (PeriodicHolderHalf.periodic data.val.2)
    parameter (label - Real.pi) (-Real.pi)
  convert identity.symm using 1 <;> congr 1 <;> ring

theorem banachContourVelocity_differentiable (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    Differentiable ℝ (banachContourVelocity data) :=
  fun label => (banachContourVelocity_hasDerivAt data small label).differentiableAt

end EulerNonuniqueness.Paper
