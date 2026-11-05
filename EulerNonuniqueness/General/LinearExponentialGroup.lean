import EulerNonuniqueness.General.LinearExponentialCurve

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def linearExponentialGroup (operator : Space →L[ℝ] Space) (time : ℝ) : Space →L[ℝ] Space :=
  NormedSpace.exp ℝ (time • operator)

theorem linearExponentialGroup_zero (operator : Space →L[ℝ] Space) :
    linearExponentialGroup operator 0 = ContinuousLinearMap.id ℝ Space := by
  simp [linearExponentialGroup]
  rfl

theorem linearExponentialGroup_add (operator : Space →L[ℝ] Space) (first second : ℝ) :
    linearExponentialGroup operator (first + second) =
      (linearExponentialGroup operator first).comp (linearExponentialGroup operator second) := by
  unfold linearExponentialGroup
  have commute : Commute (first • operator) (second • operator) := by
    apply ContinuousLinearMap.ext
    intro initial
    change first • operator (second • operator initial) = second • operator (first • operator initial)
    rw [map_smul, map_smul, smul_smul, smul_smul, mul_comm first second]
  rw [add_smul, NormedSpace.exp_add_of_commute commute]
  rfl

theorem linearExponentialGroup_hasDerivAt_left (operator : Space →L[ℝ] Space) (time : ℝ) :
    HasDerivAt (linearExponentialGroup operator) (operator.comp (linearExponentialGroup operator time)) time := by
  exact hasDerivAt_exp_smul_const' operator time

theorem linearExponentialGroup_hasDerivAt_right (operator : Space →L[ℝ] Space) (time : ℝ) :
    HasDerivAt (linearExponentialGroup operator) ((linearExponentialGroup operator time).comp operator) time := by
  exact hasDerivAt_exp_smul_const operator time

theorem linearExponentialGroup_continuous_family {operator : ℝ → Space →L[ℝ] Space}
    (continuousOperator : Continuous operator) :
    Continuous (fun pair : ℝ × ℝ => linearExponentialGroup (operator pair.1) pair.2) := by
  exact (NormedSpace.exp_continuous (𝕂 := ℝ)).comp
    (continuous_snd.smul (continuousOperator.comp continuous_fst))

end

end EulerNonuniqueness.General
