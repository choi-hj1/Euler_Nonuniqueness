import EulerNonuniqueness.Section3.ContourKernelParameter

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

set_option maxHeartbeats 1000000 in
theorem contourCauchyKernel_parameter_far_smoothness (first second : PeriodicC1HolderHalf)
    {radius jump source : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8)
    (source_far : 2 * jump ≤ |source|) (source_bounded : |source| ≤ Real.pi) :
    ‖(contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
        contourCauchyKernel second.val.1 second.val.2.val.1 0 source) -
      (contourCauchyKernel first.val.1 first.val.2.val.1 jump source -
        contourCauchyKernel second.val.1 second.val.2.val.1 jump source)‖ ≤
      ‖first - second‖ *
        (8 * (radius + 2) / (2 / (3 * Real.pi) - radius) ^ 2 +
          8 * (radius + 2) ^ 3 / (2 / (3 * Real.pi) - radius) ^ 4) * jump / |source| ^ 2 := by
  let speed := radius + 2
  let chord := 2 / (3 * Real.pi) - radius
  let constant := 2 * speed / chord ^ 2 + 2 * speed ^ 3 / chord ^ 4
  have speed_pos : 0 < speed := by dsimp only [speed]; linarith
  have chord_pos : 0 < chord := sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  have constant_nonneg : 0 ≤ constant := by dsimp only [constant]; positivity
  have source_pos : 0 < |source| := by linarith
  have first_bound : ‖first‖ ≤ speed := PeriodicC1HolderHalf.norm_le_radius_add_two first first_near
  have second_bound : ‖second‖ ≤ speed := PeriodicC1HolderHalf.norm_le_radius_add_two second second_near
  have geometry : ∀ parameter ∈ Icc 0 jump,
      |source| / 2 ≤ |parameter - source| ∧ |source - parameter| ≤ 3 * Real.pi / 2 := by
    intro parameter membership
    have parameter_abs : |parameter| = parameter := abs_of_nonneg membership.1
    have triangle : |source| ≤ |source - parameter| + |parameter| := by
      convert abs_add (source - parameter) parameter using 1
      congr 1
      ring
    have upper : |source - parameter| ≤ |source| + |parameter| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add source (-parameter)
    rw [parameter_abs, abs_sub_comm source parameter] at triangle upper
    constructor
    · linarith [membership.2]
    · rw [abs_sub_comm source parameter]
      linarith [membership.2, Real.pi_pos]
  have derivative : ∀ parameter ∈ Icc 0 jump,
      HasDerivAt (fun current => contourCauchyKernel first.val.1 first.val.2.val.1 current source -
        contourCauchyKernel second.val.1 second.val.2.val.1 current source)
        (contourCauchyKernelTargetDerivative first parameter source -
          contourCauchyKernelTargetDerivative second parameter source) parameter := by
    intro parameter membership
    have bounds := geometry parameter membership
    have distance_pos : 0 < |parameter - source| := (by linarith : 0 < |source| / 2).trans_le bounds.1
    have first_chord := PeriodicC1HolderHalf.chord_bound_of_radius first first_near bounds.2
    have second_chord := PeriodicC1HolderHalf.chord_bound_of_radius second second_near bounds.2
    rw [abs_sub_comm source parameter] at first_chord second_chord
    exact (contourCauchyKernel_hasDerivAt_target first (norm_ne_zero_iff.mp
      (ne_of_gt ((mul_pos chord_pos distance_pos).trans_le first_chord)))).sub
      (contourCauchyKernel_hasDerivAt_target second (norm_ne_zero_iff.mp
        (ne_of_gt ((mul_pos chord_pos distance_pos).trans_le second_chord))))
  have derivative_bound : ∀ parameter ∈ Icc 0 jump,
      ‖contourCauchyKernelTargetDerivative first parameter source -
        contourCauchyKernelTargetDerivative second parameter source‖ ≤
        4 * ‖first - second‖ * constant / |source| ^ 2 := by
    intro parameter membership
    have bounds := geometry parameter membership
    have distance_pos : 0 < |parameter - source| := (by linarith : 0 < |source| / 2).trans_le bounds.1
    have first_chord := PeriodicC1HolderHalf.chord_bound_of_radius first first_near bounds.2
    have second_chord := PeriodicC1HolderHalf.chord_bound_of_radius second second_near bounds.2
    rw [abs_sub_comm source parameter] at first_chord second_chord
    have actual := contourCauchyKernelTargetDerivative_parameter_bound first second
      (sub_ne_zero.mp (abs_pos.mp distance_pos)) speed_pos.le chord_pos first_bound second_bound first_chord second_chord
    apply actual.trans
    calc
      _ ≤ (‖first - second‖ * constant) / (|source| / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) bounds.1 2)
      _ = _ := by field_simp; ring
  have actual := contour_speed_bound_on_interval derivative derivative_bound
    (show (0 : ℝ) ∈ Icc 0 jump from ⟨le_rfl, jump_pos.le⟩)
    (show jump ∈ Icc 0 jump from ⟨jump_pos.le, le_rfl⟩)
  rw [sub_zero, abs_of_pos jump_pos, norm_sub_rev] at actual
  apply actual.trans_eq
  dsimp only [constant, speed, chord]
  ring

end EulerNonuniqueness.Paper
