import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

def dipoleCubicDrift (length initialDistance frequency time : ℝ) : ℝ :=
  4096 * length * (1 / initialDistance ^ 2 - 1 / (initialDistance + frequency * time) ^ 2)

theorem dipoleCubicDrift_hasDerivAt (length initialDistance frequency time : ℝ)
    (distanceNonzero : initialDistance + frequency * time ≠ 0) :
    HasDerivAt (dipoleCubicDrift length initialDistance frequency)
      (8192 * length * frequency / (initialDistance + frequency * time) ^ 3) time := by
  have linear := ((hasDerivAt_id time).const_mul frequency).const_add initialDistance
  have inverse := (hasDerivAt_const time (1 : ℝ)).div (linear.pow 2) (pow_ne_zero 2 distanceNonzero)
  have derivative := ((hasDerivAt_const time (1 / initialDistance ^ 2)).sub inverse).const_mul (4096 * length)
  convert derivative using 1 <;> dsimp [dipoleCubicDrift] <;> field_simp [distanceNonzero] <;> ring

theorem dipole_relative_speed_of_bootstrap (frequency length initialDistance time : ℝ)
    {sourceCenter targetCenter sourceSeparation targetSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length)
    (initialDistanceLarge : 16 ≤ initialDistance) (timeNonnegative : 0 ≤ time)
    (sourceBound : ‖sourceSeparation‖ ≤ 2 * length) (targetBound : ‖targetSeparation‖ ≤ 2 * length)
    (distanceBound : length * (initialDistance + frequency * time) / 4 ≤ ‖targetCenter - sourceCenter‖) :
    ‖dipoleCrossRelativeVelocity (frequency * length ^ 2) sourceCenter targetCenter sourceSeparation targetSeparation‖ ≤
      8192 * length * frequency / (initialDistance + frequency * time) ^ 3 := by
  have timeProductNonnegative := mul_nonneg frequencyPositive.le timeNonnegative
  have distancePositive : 0 < initialDistance + frequency * time := by linarith
  have centerDistancePositive : 0 < ‖targetCenter - sourceCenter‖ := lt_of_lt_of_le (by positivity) distanceBound
  have centerDistanceLower : 4 * length ≤ ‖targetCenter - sourceCenter‖ := by nlinarith
  have separationBound : ‖sourceSeparation‖ + ‖targetSeparation‖ ≤ ‖targetCenter - sourceCenter‖ := by linarith
  have control := dipoleCrossRelativeVelocity_bound (frequency * length ^ 2) centerDistancePositive separationBound
  rw [abs_of_pos (by positivity : 0 < frequency * length ^ 2)] at control
  calc
    _ ≤ 32 * (frequency * length ^ 2) * ‖sourceSeparation‖ * ‖targetSeparation‖ /
        ‖targetCenter - sourceCenter‖ ^ 3 := control
    _ ≤ 32 * (frequency * length ^ 2) * (2 * length) * (2 * length) /
        ‖targetCenter - sourceCenter‖ ^ 3 := by gcongr
    _ = 128 * frequency * length ^ 4 / ‖targetCenter - sourceCenter‖ ^ 3 := by ring
    _ ≤ 128 * frequency * length ^ 4 / (length * (initialDistance + frequency * time) / 4) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) distanceBound 3)
    _ = _ := by field_simp; ring

theorem twoDipole_first_separation_tracking
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {frequency length initialDistance horizon : ℝ} (ideal : ℂ)
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length)
    (initialDistanceLarge : 16 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target) time)
    (firstBound : ∀ time ∈ Icc 0 horizon, ‖firstSeparation time‖ ≤ 2 * length)
    (secondBound : ∀ time ∈ Icc 0 horizon, ‖secondSeparation time‖ ≤ 2 * length)
    (distanceBound : ∀ time ∈ Icc 0 horizon,
      length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖) :
    ∀ time ∈ Icc 0 horizon, ‖firstSeparation time - ideal‖ ≤
      ‖firstSeparation 0 - ideal‖ + 4096 * length / initialDistance ^ 2 := by
  have derivative := fun time member => (twoDipole_first_pair_equations (equation time member)).2
  have distancePositive (time : ℝ) (member : time ∈ Icc 0 horizon) :
      0 < initialDistance + frequency * time := by nlinarith [mul_nonneg frequencyPositive.le member.1]
  have pathContinuous : ContinuousOn (fun time => firstSeparation time - ideal) (Icc 0 horizon) := by
    intro time member
    exact ((derivative time member).continuousAt.sub continuousAt_const).continuousWithinAt
  have pathDerivative := fun time (member : time ∈ Ico 0 horizon) =>
    ((derivative time ⟨member.1, member.2.le⟩).sub_const ideal).hasDerivWithinAt (s := Ici time)
  let barrier := fun time => ‖firstSeparation 0 - ideal‖ + dipoleCubicDrift length initialDistance frequency time
  have barrierContinuous : ContinuousOn barrier (Icc 0 horizon) := by
    intro time member
    exact (continuousAt_const.add (dipoleCubicDrift_hasDerivAt length initialDistance frequency time
      (distancePositive time member).ne').continuousAt).continuousWithinAt
  have barrierDerivative := fun time (member : time ∈ Ico 0 horizon) =>
    ((dipoleCubicDrift_hasDerivAt length initialDistance frequency time
      (distancePositive time ⟨member.1, member.2.le⟩).ne').const_add ‖firstSeparation 0 - ideal‖).hasDerivWithinAt (s := Ici time)
  have control := image_norm_le_of_norm_deriv_right_le_deriv_boundary' pathContinuous pathDerivative
    (B := barrier) (by simp [barrier, dipoleCubicDrift]) barrierContinuous barrierDerivative (by
      intro time member
      exact dipole_relative_speed_of_bootstrap frequency length initialDistance time frequencyPositive lengthPositive
        initialDistanceLarge member.1 (secondBound time ⟨member.1, member.2.le⟩)
        (firstBound time ⟨member.1, member.2.le⟩) (distanceBound time ⟨member.1, member.2.le⟩))
  intro time member
  apply (control member).trans
  dsimp only [barrier, dipoleCubicDrift]
  apply add_le_add_left
  calc
    _ = 4096 * length / initialDistance ^ 2 - 4096 * length / (initialDistance + frequency * time) ^ 2 := by ring
    _ ≤ _ := sub_le_self _ (by positivity)

theorem twoDipole_second_separation_tracking
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {frequency length initialDistance horizon : ℝ} (ideal : ℂ)
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length)
    (initialDistanceLarge : 16 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target) time)
    (firstBound : ∀ time ∈ Icc 0 horizon, ‖firstSeparation time‖ ≤ 2 * length)
    (secondBound : ∀ time ∈ Icc 0 horizon, ‖secondSeparation time‖ ≤ 2 * length)
    (distanceBound : ∀ time ∈ Icc 0 horizon,
      length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖) :
    ∀ time ∈ Icc 0 horizon, ‖secondSeparation time - ideal‖ ≤
      ‖secondSeparation 0 - ideal‖ + 4096 * length / initialDistance ^ 2 := by
  have switchedEquation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (secondCenter current) (firstCenter current)
        (secondSeparation current) (firstSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (secondCenter time) (firstCenter time)
          (secondSeparation time) (firstSeparation time)) target) time := by
    intro time member target
    have firstEquation := equation time member 1
    have secondEquation := equation time member 0
    have thirdEquation := equation time member 3
    have fourthEquation := equation time member 2
    rw [fourPointField_twoDipoles] at firstEquation secondEquation thirdEquation fourthEquation ⊢
    fin_cases target
    · simpa [twoDipoleConfiguration] using firstEquation
    · simpa [twoDipoleConfiguration] using secondEquation
    · simpa [twoDipoleConfiguration] using thirdEquation
    · simpa [twoDipoleConfiguration] using fourthEquation
  exact twoDipole_first_separation_tracking ideal frequencyPositive lengthPositive initialDistanceLarge
    horizonNonnegative switchedEquation secondBound firstBound
    (fun time member => by simpa only [norm_sub_rev] using distanceBound time member)

end EulerNonuniqueness.Section6
