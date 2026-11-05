import EulerNonuniqueness.General.QuadraticGroupConjugation

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def quadraticCoordinate (correction : BilinearEnd Space) (frequency : ℝ) (value : Space) : Space :=
  value - (1 / frequency : ℝ) • correction value value

theorem quadratic_coordinate_velocity
    (generator : Space →L[ℝ] Space) (quadratic correction resonant : BilinearEnd Space)
    {frequency : ℝ} (frequencyNonzero : frequency ≠ 0)
    (homological : quadraticCommutator generator correction = quadratic - resonant)
    (value remainder : Space) :
    (frequency • generator value + quadratic value value + remainder) - (1 / frequency : ℝ) •
        (correction (frequency • generator value + quadratic value value + remainder) value +
          correction value (frequency • generator value + quadratic value value + remainder)) =
      frequency • generator (quadraticCoordinate correction frequency value) + resonant value value + remainder -
        (1 / frequency : ℝ) • (correction (quadratic value value + remainder) value +
          correction value (quadratic value value + remainder)) := by
  have evaluated := congrArg (fun bilinear : BilinearEnd Space => bilinear value value) homological
  change -generator (correction value value) + correction (generator value) value +
    correction value (generator value) = quadratic value value - resonant value value at evaluated
  have linearRelation :
      (correction (generator value) value + correction value (generator value)) - generator (correction value value) =
        quadratic value value - resonant value value := by
    convert evaluated using 1 <;> abel
  have linearIdentity := (sub_eq_iff_eq_add).mp linearRelation
  have derivativePair : correction (frequency • generator value + quadratic value value + remainder) value +
      correction value (frequency • generator value + quadratic value value + remainder) =
      frequency • (correction (generator value) value + correction value (generator value)) +
        (correction (quadratic value value + remainder) value + correction value (quadratic value value + remainder)) := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    module
  rw [derivativePair, linearIdentity]
  simp only [quadraticCoordinate, map_sub, map_smul, smul_add, smul_sub, smul_smul,
    one_div, inv_mul_cancel₀ frequencyNonzero, mul_inv_cancel₀ frequencyNonzero, one_smul]
  abel

theorem quadratic_coordinate_hasDerivAt
    (generator : Space →L[ℝ] Space) (quadratic correction resonant : BilinearEnd Space)
    {frequency time : ℝ} {trajectory : ℝ → Space} {remainder : Space}
    (frequencyNonzero : frequency ≠ 0)
    (homological : quadraticCommutator generator correction = quadratic - resonant)
    (equation : HasDerivAt trajectory
      (frequency • generator (trajectory time) + quadratic (trajectory time) (trajectory time) + remainder) time) :
    HasDerivAt (fun current => quadraticCoordinate correction frequency (trajectory current))
      (frequency • generator (quadraticCoordinate correction frequency (trajectory time)) +
        resonant (trajectory time) (trajectory time) + remainder -
          (1 / frequency : ℝ) • (correction (quadratic (trajectory time) (trajectory time) + remainder) (trajectory time) +
            correction (trajectory time) (quadratic (trajectory time) (trajectory time) + remainder))) time := by
  have first := HasFDerivAt.comp_hasDerivAt (F := Space) (E := Space →L[ℝ] Space)
    (f := trajectory) time (ContinuousLinearMap.hasFDerivAt correction) equation
  have paired := first.clm_apply equation
  have changed := equation.sub (paired.const_smul (1 / frequency : ℝ))
  simp only [Function.comp_apply] at changed
  rw [quadratic_coordinate_velocity generator quadratic correction resonant frequencyNonzero homological] at changed
  exact changed

theorem quadraticCoordinate_sub_norm_le (correction : BilinearEnd Space) (frequency : ℝ) (value : Space) :
    ‖quadraticCoordinate correction frequency value - value‖ ≤
      (‖correction‖ / |frequency|) * ‖value‖ ^ 2 := by
  rw [quadraticCoordinate, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_one]
  calc
    _ ≤ (1 / |frequency|) * (‖correction‖ * ‖value‖ * ‖value‖) :=
      mul_le_mul_of_nonneg_left (correction.le_opNorm₂ value value) (by positivity)
    _ = _ := by ring

theorem quadraticCoordinate_nonlinear_error_norm_le
    (quadratic correction : BilinearEnd Space) (frequency : ℝ) (value remainder : Space) :
    ‖(1 / frequency : ℝ) • (correction (quadratic value value + remainder) value +
      correction value (quadratic value value + remainder))‖ ≤
      (2 * ‖correction‖ / |frequency|) * (‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖) * ‖value‖ := by
  have sourceBound : ‖quadratic value value + remainder‖ ≤ ‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖ := by
    apply (norm_add_le _ _).trans
    exact add_le_add_right (by simpa only [pow_two, mul_assoc] using quadratic.le_opNorm₂ value value) _
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_one]
  calc
    _ ≤ (1 / |frequency|) * (‖correction (quadratic value value + remainder) value‖ +
        ‖correction value (quadratic value value + remainder)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1 / |frequency|) * (‖correction‖ * ‖quadratic value value + remainder‖ * ‖value‖ +
        ‖correction‖ * ‖value‖ * ‖quadratic value value + remainder‖) := by
      gcongr
      · exact correction.le_opNorm₂ _ _
      · exact correction.le_opNorm₂ _ _
    _ ≤ (1 / |frequency|) * (‖correction‖ * (‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖) * ‖value‖ +
        ‖correction‖ * ‖value‖ * (‖quadratic‖ * ‖value‖ ^ 2 + ‖remainder‖)) := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.General
