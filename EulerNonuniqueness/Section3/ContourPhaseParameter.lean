import EulerNonuniqueness.Section3.ContourBanachBounds

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem complex_phase_difference_bound {first second : ℂ} (first_ne : first ≠ 0)
    (second_ne : second ≠ 0) :
    ‖first / star first - second / star second‖ ≤ 2 * ‖first - second‖ / ‖first‖ := by
  have first_star_ne : star first ≠ 0 := star_ne_zero.mpr first_ne
  have second_star_ne : star second ≠ 0 := star_ne_zero.mpr second_ne
  have identity : first / star first - second / star second =
      ((first - second) * star second - second * star (first - second)) /
        (star first * star second) := by
    rw [star_sub]
    field_simp [Complex.star_def, first_ne, second_ne]
    ring
  rw [identity, norm_div, norm_mul, norm_star, norm_star]
  have positive : 0 < ‖first‖ * ‖second‖ :=
    mul_pos (norm_pos_iff.mpr first_ne) (norm_pos_iff.mpr second_ne)
  apply (div_le_iff₀ positive).mpr
  calc
    _ ≤ ‖(first - second) * star second‖ + ‖second * star (first - second)‖ := norm_sub_le _ _
    _ = 2 * ‖first - second‖ * ‖second‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]; ring
    _ = _ := by field_simp; ring

theorem PeriodicC1HolderHalf.lipschitz_bound (data : PeriodicC1HolderHalf) (first second : ℝ) :
    ‖data.val.1 first - data.val.1 second‖ ≤ ‖data‖ * |first - second| := by
  exact contour_speed_bound_on_interval
    (lower := min first second) (upper := max first second)
    (fun current _ => PeriodicC1HolderHalf.hasDerivAt data current)
    (fun current _ => PeriodicC1HolderHalf.speed_bound data current)
    ⟨min_le_right _ _, le_max_right _ _⟩ ⟨min_le_left _ _, le_max_left _ _⟩

theorem PeriodicC1HolderHalf.increment_difference_bound (first second : PeriodicC1HolderHalf)
    (target source : ℝ) :
    ‖(first.val.1 target - first.val.1 source) - (second.val.1 target - second.val.1 source)‖ ≤
      ‖first - second‖ * |target - source| := by
  have actual := PeriodicC1HolderHalf.lipschitz_bound (first - second) target source
  convert actual using 1
  congr 1
  change (first.val.1 target - first.val.1 source) - (second.val.1 target - second.val.1 source) =
    (first.val.1 target - second.val.1 target) - (first.val.1 source - second.val.1 source)
  abel

theorem contourChordPhase_parameter_bound (first second : PeriodicC1HolderHalf)
    {target source chord : ℝ} (chord_pos : 0 < chord)
    (first_chord : chord * |target - source| ≤ ‖first.val.1 target - first.val.1 source‖)
    (second_separated : target ≠ source → second.val.1 target - second.val.1 source ≠ 0) :
    ‖contourChordPhase first.val.1 target source - contourChordPhase second.val.1 target source‖ ≤
      (2 / chord) * ‖first - second‖ := by
  by_cases equal : target = source
  · subst source
    simp only [contourChordPhase, sub_self, star_zero, div_zero, norm_zero]
    positivity
  have distance_pos := abs_pos.mpr (sub_ne_zero.mpr equal)
  have first_pos := (mul_pos chord_pos distance_pos).trans_le first_chord
  have phase_bound := complex_phase_difference_bound
    (norm_ne_zero_iff.mp first_pos.ne') (second_separated equal)
  change ‖_‖ ≤ _
  apply phase_bound.trans
  calc
    _ ≤ (2 * (‖first - second‖ * |target - source|)) / ‖first.val.1 target - first.val.1 source‖ :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (PeriodicC1HolderHalf.increment_difference_bound first second target source)
          (by norm_num)) (norm_nonneg _)
    _ ≤ (2 * (‖first - second‖ * |target - source|)) / (chord * |target - source|) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos chord_pos distance_pos) first_chord
    _ = _ := by field_simp; ring

theorem contourChordPhase_integrand_parameter_bound (first second : PeriodicC1HolderHalf)
    {target source chord : ℝ} (chord_pos : 0 < chord)
    (first_chord : chord * |target - source| ≤ ‖first.val.1 target - first.val.1 source‖)
    (second_separated : target ≠ source → second.val.1 target - second.val.1 source ≠ 0) :
    ‖contourChordPhase first.val.1 target source * star (first.val.2.val.1 source) -
      contourChordPhase second.val.1 target source * star (second.val.2.val.1 source)‖ ≤
      (1 + 2 * ‖second‖ / chord) * ‖first - second‖ := by
  have identity : contourChordPhase first.val.1 target source * star (first.val.2.val.1 source) -
      contourChordPhase second.val.1 target source * star (second.val.2.val.1 source) =
      contourChordPhase first.val.1 target source * star (first.val.2.val.1 source - second.val.2.val.1 source) +
      (contourChordPhase first.val.1 target source - contourChordPhase second.val.1 target source) *
        star (second.val.2.val.1 source) := by rw [star_sub]; ring
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_star, norm_star]
  have speed_difference : ‖first.val.2.val.1 source - second.val.2.val.1 source‖ ≤ ‖first - second‖ :=
    PeriodicC1HolderHalf.speed_bound (first - second) source
  calc
    _ ≤ 1 * ‖first - second‖ + ((2 / chord) * ‖first - second‖) * ‖second‖ :=
      add_le_add
        (mul_le_mul (contourChordPhase_norm_le_one _ _ _) speed_difference (norm_nonneg _) (by norm_num))
        (mul_le_mul (contourChordPhase_parameter_bound first second chord_pos first_chord second_separated)
          (PeriodicC1HolderHalf.speed_bound second source) (norm_nonneg _) (by positivity))
    _ = _ := by ring

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem banachContourVelocity_eq_phase (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    banachContourVelocity data label = (1 / (4 * Real.pi)) •
      ∫ source in (label - Real.pi)..(label + Real.pi),
        contourChordPhase data.val.1 label source * star (data.val.2.val.1 source) := by
  have window := contourVelocity_periodic_source_window
    (PeriodicC1HolderHalf.periodic data) (PeriodicHolderHalf.periodic data.val.2)
    label (-Real.pi) (label - Real.pi)
  have window_identity : banachContourVelocity data label =
      contourVelocity data.val.1 data.val.2.val.1 label (label - Real.pi) (label + Real.pi) := by
    unfold banachContourVelocity
    convert window using 1 <;> congr 1 <;> ring
  rw [window_identity]
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
  rw [phase, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : label - Real.pi ≤ label + Real.pi)]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem banachContourVelocity_parameter_bound (first second : PeriodicC1HolderHalf)
    (first_small : ‖first - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (second_small : ‖second - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    ‖banachContourVelocity first label - banachContourVelocity second label‖ ≤
      ((1 + 2 * ‖second‖ / (2 / (3 * Real.pi) - ‖first - standardCircleBanach‖)) / 2) *
        ‖first - second‖ := by
  let chord := 2 / (3 * Real.pi) - ‖first - standardCircleBanach‖
  have chord_pos : 0 < chord := sub_pos.mpr (first_small.trans_le (min_le_right _ _))
  have second_chord_pos : 0 < 2 / (3 * Real.pi) - ‖second - standardCircleBanach‖ :=
    sub_pos.mpr (second_small.trans_le (min_le_right _ _))
  have ordered : label - Real.pi ≤ label + Real.pi := by linarith [Real.pi_pos]
  have integrable : ∀ data : PeriodicC1HolderHalf, IntervalIntegrable
      (fun source => contourChordPhase data.val.1 label source * star (data.val.2.val.1 source))
      volume (label - Real.pi) (label + Real.pi) := by
    intro data
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr
      (contourChordPhase_integrable data.val.1.continuous data.val.2.val.1.continuous
        (fun source _ => PeriodicC1HolderHalf.speed_bound data source))
  rw [banachContourVelocity_eq_phase first first_small label, banachContourVelocity_eq_phase second second_small label,
    ← smul_sub, ← intervalIntegral.integral_sub (integrable first) (integrable second), norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (4 * Real.pi))]
  have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := label - Real.pi) (b := label + Real.pi)
    (f := fun source => contourChordPhase first.val.1 label source * star (first.val.2.val.1 source) -
      contourChordPhase second.val.1 label source * star (second.val.2.val.1 source))
    (C := (1 + 2 * ‖second‖ / chord) * ‖first - second‖) (fun source membership => by
      have source_mem : source ∈ Icc (label - Real.pi) (label + Real.pi) := by
        have direct : source ∈ Ioc (label - Real.pi) (label + Real.pi) := by
          simpa only [uIoc_of_le ordered] using membership
        exact ⟨direct.1.le, direct.2⟩
      have nearby : |source - label| ≤ 3 * Real.pi / 2 := by
        rw [abs_le]
        constructor <;> linarith [source_mem.1, source_mem.2, Real.pi_pos]
      exact contourChordPhase_integrand_parameter_bound first second chord_pos
        (by simpa only [abs_sub_comm label source] using PeriodicC1HolderHalf.chord_bound_extended first nearby)
        (fun distinct => norm_ne_zero_iff.mp (ne_of_gt ((mul_pos second_chord_pos
          (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
            (by simpa only [abs_sub_comm label source] using
              PeriodicC1HolderHalf.chord_bound_extended second nearby)))))
  have length : |label + Real.pi - (label - Real.pi)| = 2 * Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  rw [length] at estimate
  apply (mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ 1 / (4 * Real.pi))).trans_eq
  dsimp only [chord]
  field_simp
  ring

theorem boundedBanachContourVelocity_parameter_bound (first second : PeriodicC1HolderHalf)
    (first_small : ‖first - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (second_small : ‖second - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    ‖boundedBanachContourVelocity first first_small - boundedBanachContourVelocity second second_small‖ ≤
      ((1 + 2 * ‖second‖ / (2 / (3 * Real.pi) - ‖first - standardCircleBanach‖)) / 2) *
        ‖first - second‖ := by
  apply (BoundedContinuousFunction.norm_le (by
    have positive := sub_pos.mpr (first_small.trans_le (min_le_right _ _))
    positivity)).mpr
  intro label
  exact banachContourVelocity_parameter_bound first second first_small second_small label

theorem boundedBanachContourVelocity_uniform_parameter_bound (first second : PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖boundedBanachContourVelocity first (first_near.trans_lt radius_small) -
      boundedBanachContourVelocity second (second_near.trans_lt radius_small)‖ ≤
      ((1 + 2 * (radius + 2) / (2 / (3 * Real.pi) - radius)) / 2) * ‖first - second‖ := by
  have denominator_pos : 0 < 2 / (3 * Real.pi) - radius :=
    sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  have denominator_bound : 2 / (3 * Real.pi) - radius ≤
      2 / (3 * Real.pi) - ‖first - standardCircleBanach‖ := by linarith
  have second_bound : ‖second‖ ≤ radius + 2 := by
    have triangle := norm_add_le (second - standardCircleBanach) standardCircleBanach
    rw [sub_add_cancel second standardCircleBanach] at triangle
    linarith [standardCircleBanach_norm_bound]
  have coefficient_bound :
      (1 + 2 * ‖second‖ / (2 / (3 * Real.pi) - ‖first - standardCircleBanach‖)) / 2 ≤
        (1 + 2 * (radius + 2) / (2 / (3 * Real.pi) - radius)) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add_left
    exact (div_le_div_of_nonneg_left (by positivity) denominator_pos denominator_bound).trans
      (div_le_div_of_nonneg_right (by linarith) denominator_pos.le)
  exact (boundedBanachContourVelocity_parameter_bound first second
    (first_near.trans_lt radius_small) (second_near.trans_lt radius_small)).trans
      (mul_le_mul_of_nonneg_right coefficient_bound (norm_nonneg _))

end EulerNonuniqueness.Paper
