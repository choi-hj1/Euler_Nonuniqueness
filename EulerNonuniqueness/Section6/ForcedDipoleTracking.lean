import EulerNonuniqueness.Section6.ForcedTwoDipoleDynamics

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem norm_drift_of_cubic_derivative_bound {trajectory velocity : ℝ → ℂ}
    {frequency length initialDistance horizon rate : ℝ} (ideal : ℂ)
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length)
    (initialDistancePositive : 0 < initialDistance)
    (equation : ∀ time ∈ Icc 0 horizon, HasDerivAt trajectory (velocity time) time)
    (velocityBound : ∀ time ∈ Ico 0 horizon, ‖velocity time‖ ≤
      8192 * length * frequency / (initialDistance + frequency * time) ^ 3 + rate) :
    ∀ time ∈ Icc 0 horizon, ‖trajectory time - ideal‖ ≤
      ‖trajectory 0 - ideal‖ + 4096 * length / initialDistance ^ 2 + rate * time := by
  have distancePositive (time : ℝ) (member : time ∈ Icc 0 horizon) :
      0 < initialDistance + frequency * time := by nlinarith [mul_nonneg frequencyPositive.le member.1]
  let barrier := fun time => ‖trajectory 0 - ideal‖ + dipoleCubicDrift length initialDistance frequency time + rate * time
  have barrierDerivative (time : ℝ) (member : time ∈ Icc 0 horizon) : HasDerivAt barrier
      (8192 * length * frequency / (initialDistance + frequency * time) ^ 3 + rate) time := by
    have linear : HasDerivAt (fun current : ℝ => rate * current) rate time := by
      simpa using (hasDerivAt_id time).const_mul rate
    exact ((dipoleCubicDrift_hasDerivAt length initialDistance frequency time
      (distancePositive time member).ne').const_add ‖trajectory 0 - ideal‖).add linear
  have control := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (fun time member => ((equation time member).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun time member => ((equation time ⟨member.1, member.2.le⟩).sub_const ideal).hasDerivWithinAt (s := Ici time))
    (B := barrier) (by simp [barrier, dipoleCubicDrift])
    (fun time member => (barrierDerivative time member).continuousAt.continuousWithinAt)
    (fun time member => (barrierDerivative time ⟨member.1, member.2.le⟩).hasDerivWithinAt (s := Ici time)) velocityBound
  intro time member
  apply (control member).trans
  dsimp only [barrier, dipoleCubicDrift]
  have cubicBound : 4096 * length * (1 / initialDistance ^ 2 - 1 / (initialDistance + frequency * time) ^ 2) ≤
      4096 * length / initialDistance ^ 2 := by
    calc
      _ = 4096 * length / initialDistance ^ 2 - 4096 * length / (initialDistance + frequency * time) ^ 2 := by ring
      _ ≤ _ := sub_le_self _ (by positivity)
  linarith

theorem dipole_forced_relative_speed_bound {cross external : ℂ} {residual : FourPointConfiguration}
    {positive negative : Fin 4} {cubic strain length error : ℝ}
    (strainNonnegative : 0 ≤ strain) (lengthNonnegative : 0 ≤ length)
    (crossBound : ‖cross‖ ≤ cubic) (externalBound : ‖external‖ ≤ 2 * strain * length)
    (residualBound : ‖residual‖ ≤ error * length) :
    ‖cross + external + residual positive - residual negative‖ ≤ cubic + 2 * (strain + error) * length := by
  have identity : cross + external + residual positive - residual negative =
      (cross + external) + (residual positive - residual negative) := by ring
  rw [identity]
  have triangle := norm_add_le (cross + external) (residual positive - residual negative)
  have crossTriangle := norm_add_le cross external
  have residualControl := residual_pair_difference_bound residual positive negative
  linarith

theorem twoDipole_forced_separation_tracking
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {residual : ℝ → FourPointConfiguration} {region : ℝ → Set ℂ}
    {frequency length initialDistance horizon error : ℝ} {strain : ℝ≥0} (firstIdeal secondIdeal : ℂ)
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (initialDistanceLarge : 16 ≤ initialDistance)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2) (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target +
        external time (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual time target) time)
    (externalLipschitz : ∀ time ∈ Icc 0 horizon, LipschitzOnWith strain (external time) (region time))
    (inside : ∀ time ∈ Icc 0 horizon, ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region time)
    (residualBound : ∀ time ∈ Icc 0 horizon, ‖residual time‖ ≤ error * length)
    (firstBound : ∀ time ∈ Icc 0 horizon, ‖firstSeparation time‖ ≤ 2 * length)
    (secondBound : ∀ time ∈ Icc 0 horizon, ‖secondSeparation time‖ ≤ 2 * length)
    (distanceBound : ∀ time ∈ Icc 0 horizon,
      length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖) :
    ∀ time ∈ Icc 0 horizon,
      ‖firstSeparation time - firstIdeal‖ ≤ ‖firstSeparation 0 - firstIdeal‖ +
        4096 * length / initialDistance ^ 2 + 2 * ((strain : ℝ) + error) * length * time ∧
      ‖secondSeparation time - secondIdeal‖ ≤ ‖secondSeparation 0 - secondIdeal‖ +
        4096 * length / initialDistance ^ 2 + 2 * ((strain : ℝ) + error) * length * time := by
  have firstDerivative := fun time member => (twoDipole_first_pair_forced_equations (equation time member)).2
  have secondDerivative (time : ℝ) (member : time ∈ Icc 0 horizon) : HasDerivAt secondSeparation
      (dipoleCrossRelativeVelocity (frequency * length ^ 2) (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time) +
        externalPairDifference (external time) (secondCenter time) (secondSeparation time) +
          residual time 1 - residual time 3) time := by
    have positiveEquation := equation time member 1
    have negativeEquation := equation time member 3
    rw [fourPointField_twoDipoles] at positiveEquation negativeEquation
    simp only [twoDipoleConfiguration, Matrix.cons_val_zero, Matrix.cons_val_succ] at positiveEquation negativeEquation
    convert positiveEquation.sub negativeEquation using 1
    · funext current
      simp [twoDipoleConfiguration] <;> ring
    · dsimp [dipoleCrossRelativeVelocity, externalPairDifference]
      ring
  have firstControl := norm_drift_of_cubic_derivative_bound firstIdeal frequencyPositive lengthPositive
    (by linarith : 0 < initialDistance) firstDerivative (by
      intro time member
      have memberClosed : time ∈ Icc 0 horizon := ⟨member.1, member.2.le⟩
      have crossControl := dipole_relative_speed_of_bootstrap frequency length initialDistance time frequencyPositive lengthPositive
        initialDistanceLarge member.1 (secondBound time memberClosed) (firstBound time memberClosed) (distanceBound time memberClosed)
      have externalControl := externalPairDifference_bound (externalLipschitz time memberClosed)
        (by simpa [twoDipoleConfiguration] using inside time memberClosed 0)
        (by simpa [twoDipoleConfiguration] using inside time memberClosed 2)
      apply dipole_forced_relative_speed_bound strain.coe_nonneg lengthPositive.le crossControl
        (externalControl.trans ?_) (residualBound time memberClosed)
      nlinarith [mul_le_mul_of_nonneg_left (firstBound time memberClosed) strain.coe_nonneg])
  have secondControl := norm_drift_of_cubic_derivative_bound secondIdeal frequencyPositive lengthPositive
    (by linarith : 0 < initialDistance) secondDerivative (by
      intro time member
      have memberClosed : time ∈ Icc 0 horizon := ⟨member.1, member.2.le⟩
      have crossControl := dipole_relative_speed_of_bootstrap frequency length initialDistance time frequencyPositive lengthPositive
        initialDistanceLarge member.1 (firstBound time memberClosed) (secondBound time memberClosed)
        (by simpa only [norm_sub_rev] using distanceBound time memberClosed)
      have externalControl := externalPairDifference_bound (externalLipschitz time memberClosed)
        (by simpa [twoDipoleConfiguration] using inside time memberClosed 1)
        (by simpa [twoDipoleConfiguration] using inside time memberClosed 3)
      apply dipole_forced_relative_speed_bound strain.coe_nonneg lengthPositive.le crossControl
        (externalControl.trans ?_) (residualBound time memberClosed)
      nlinarith [mul_le_mul_of_nonneg_left (secondBound time memberClosed) strain.coe_nonneg])
  exact fun time member => ⟨firstControl time member, secondControl time member⟩

end EulerNonuniqueness.Section6
