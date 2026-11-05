import EulerNonuniqueness.Section6.FourPointPassageStability
import EulerNonuniqueness.Section6.FourPointTranslationControl

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointCenterProjection (positions : FourPointConfiguration) : FourPointConfiguration :=
  fun target => positions target - fourPointArithmeticCenter positions

theorem fourPointCenterProjection_sub (first second : FourPointConfiguration) :
    fourPointCenterProjection (first - second) =
      fourPointCenterProjection first - fourPointCenterProjection second := by
  funext target
  simp only [fourPointCenterProjection, Pi.sub_apply, fourPointArithmeticCenter_sub]
  ring

theorem fourPointCenterProjection_add (first second : FourPointConfiguration) :
    fourPointCenterProjection (first + second) =
      fourPointCenterProjection first + fourPointCenterProjection second := by
  funext target
  simp only [fourPointCenterProjection, Pi.add_apply, fourPointArithmeticCenter,
    Finset.sum_add_distrib, add_div]
  ring

theorem fourPointCenterProjection_norm_le (positions : FourPointConfiguration) :
    ‖fourPointCenterProjection positions‖ ≤ 2 * ‖positions‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro target
  exact (norm_sub_le _ _).trans (by
    linarith [norm_le_pi_norm positions target, fourPointArithmeticCenter_norm_le positions])

theorem fourPointCenterProjection_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {velocity : FourPointConfiguration} {time : ℝ} (equation : HasDerivAt trajectory velocity time) :
    HasDerivAt (fun current => fourPointCenterProjection (trajectory current))
      (fourPointCenterProjection velocity) time := by
  have average := (HasDerivAt.sum (u := Finset.univ)
    (fun target _ => hasDerivAt_pi.mp equation target)).div_const 4
  apply hasDerivAt_pi.mpr
  intro target
  exact (hasDerivAt_pi.mp equation target).sub average

def fourPointCenteredField (coefficient : ℝ) (positions : FourPointConfiguration) : FourPointConfiguration :=
  fourPointCenterProjection (fourPointField coefficient positions)

theorem fourPointField_centerProjection (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointField coefficient (fourPointCenterProjection positions) = fourPointField coefficient positions := by
  have actual := fourPointField_translation_invariant coefficient positions (-fourPointArithmeticCenter positions)
  simpa only [fourPointCenterProjection, Pi.add_def, sub_eq_add_neg] using actual

theorem fourPointCenteredField_difference_le {coefficient gap : ℝ} (gapPositive : 0 < gap)
    (first second : FourPointConfiguration)
    (firstSeparated : ∀ target source, source ≠ target → gap ≤ ‖first target - first source‖)
    (secondSeparated : ∀ target source, source ≠ target → gap ≤ ‖second target - second source‖) :
    ‖fourPointCenteredField coefficient first - fourPointCenteredField coefficient second‖ ≤
      (16 * |coefficient| / gap ^ 2) * ‖first - second‖ := by
  rw [fourPointCenteredField, fourPointCenteredField, ← fourPointCenterProjection_sub]
  exact (fourPointCenterProjection_norm_le _).trans
    ((mul_le_mul_of_nonneg_left (fourPointField_difference_le gapPositive first second firstSeparated secondSeparated)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

theorem fourPointCenteredField_centerProjection (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointCenteredField coefficient (fourPointCenterProjection positions) = fourPointCenteredField coefficient positions := by
  rw [fourPointCenteredField, fourPointField_centerProjection]
  rfl

theorem fourPointCenterProjection_forced_equation {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (equation : HasDerivAt trajectory (fourPointField coefficient (trajectory time) + forcing) time) :
    HasDerivAt (fun current => fourPointCenterProjection (trajectory current))
      (fourPointCenteredField coefficient (fourPointCenterProjection (trajectory time)) +
        fourPointCenterProjection forcing) time := by
  have actual := fourPointCenterProjection_hasDerivAt equation
  rw [fourPointCenterProjection_add] at actual
  simpa only [fourPointCenteredField, fourPointField_centerProjection] using actual

end EulerNonuniqueness.Section6
