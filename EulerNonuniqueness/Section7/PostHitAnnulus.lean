import EulerNonuniqueness.Section6.DipoleMidpointDrift
import EulerNonuniqueness.General.MidpointAnnulus

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section7

open Section6

theorem twoDipole_domain_annular_estimate
    {firstCenter secondCenter firstSeparation secondSeparation center : ℂ}
    {domain : Fin 4 → Set ℂ} {length domainRadius centerError : ℝ}
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (centerControl : ‖(firstCenter + secondCenter) / 2 - center‖ ≤ centerError)
    (domains : ∀ target, domain target ⊆ Metric.closedBall
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target) domainRadius)
    (target : Fin 4) (position : ℂ) (member : position ∈ domain target) :
    ‖firstCenter - secondCenter‖ / 2 - domainRadius - length - centerError ≤ ‖position - center‖ ∧
      ‖position - center‖ ≤ ‖firstCenter - secondCenter‖ / 2 + domainRadius + length + centerError := by
  let pairCenter := if target = 0 ∨ target = 2 then firstCenter else secondCenter
  have pointNear : dist (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target)
      pairCenter ≤ length := by
    fin_cases target <;> simp [pairCenter, twoDipoleConfiguration, dist_eq_norm, norm_div]
    all_goals linarith
  have localBound : dist position pairCenter ≤ domainRadius + length :=
    (dist_triangle position (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target)
      pairCenter).trans (add_le_add (domains target member) pointNear)
  have midpointIdentity : midpoint ℝ firstCenter secondCenter = (firstCenter + secondCenter) / 2 := by
    simp [midpoint_eq_smul_add, invOf_eq_inv, Complex.real_smul]
    ring
  have nearMiddle : dist center (midpoint ℝ firstCenter secondCenter) ≤ centerError := by
    rw [midpointIdentity, dist_comm, dist_eq_norm]
    exact centerControl
  by_cases firstPair : target = 0 ∨ target = 2
  · have estimate := dist_annulus_of_dist_midpoint_le (space := ℂ)
      (first := firstCenter) (second := secondCenter) (position := position) (center := center)
      (by simpa only [pairCenter, if_pos firstPair] using localBound) nearMiddle
    rw [dist_eq_norm, dist_eq_norm] at estimate
    constructor <;> linarith [estimate.1, estimate.2]
  · have secondNear : dist center (midpoint ℝ secondCenter firstCenter) ≤ centerError := by
      rw [midpoint_comm]
      exact nearMiddle
    have estimate := dist_annulus_of_dist_midpoint_le (space := ℂ)
      (first := secondCenter) (second := firstCenter) (position := position) (center := center)
      (by simpa only [pairCenter, if_neg firstPair] using localBound)
      secondNear
    rw [dist_comm secondCenter firstCenter, dist_eq_norm, dist_eq_norm] at estimate
    constructor <;> linarith [estimate.1, estimate.2]

theorem twoDipole_forced_posthit_domain_annulus
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {residual : ℝ → FourPointConfiguration} {region : ℝ → Set ℂ}
    {domain : Fin 4 → Set ℂ} {center direction : ℂ}
    {frequency length initialDistance horizon error externalBound domainRadius initialCenterError : ℝ}
    {strain : ℝ≥0}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (initialDistanceSmall : initialDistance ≤ frequency / 16)
    (horizonLower : 1 / 2 ≤ horizon) (horizonUpper : horizon ≤ 1)
    (errorNonnegative : 0 ≤ error) (externalNonnegative : 0 ≤ externalBound)
    (relativeSmall : 64 * ((strain : ℝ) + error) * horizon ≤ 1)
    (centerSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2)
    (translationSmall : externalBound + error * length ≤ frequency * length / 32)
    (initialCenter : ‖(firstCenter 0 + secondCenter 0) / 2 - center‖ ≤ initialCenterError)
    (initialCenterSmall : length + initialCenterError + domainRadius ≤ frequency * length / 64)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target + external time
            (twoDipoleConfiguration (firstCenter time) (secondCenter time)
              (firstSeparation time) (secondSeparation time) target) + residual time target) time)
    (externalLipschitz : ∀ time ∈ Icc 0 horizon, LipschitzOnWith strain (external time) (region time))
    (inside : ∀ time ∈ Icc 0 horizon, ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region time)
    (externalControl : ∀ time ∈ Icc 0 horizon, ∀ target,
      ‖external time (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time) target)‖ ≤ externalBound)
    (residualControl : ∀ time ∈ Icc 0 horizon, ‖residual time‖ ≤ error * length)
    (firstInitial : ‖firstSeparation 0 - (length : ℂ) * direction‖ ≤ length / 64)
    (secondInitial : ‖secondSeparation 0 - (length : ℂ) * (-direction)‖ ≤ length / 64)
    (initialProjection : (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤ (5 / 4 : ℝ) * length * initialDistance)
    (domains : ∀ target, domain target ⊆ Metric.closedBall
      (twoDipoleConfiguration (firstCenter horizon) (secondCenter horizon)
        (firstSeparation horizon) (secondSeparation horizon) target) domainRadius) :
    ∀ target position, position ∈ domain target →
      frequency * length / 16 ≤ ‖position - center‖ ∧ ‖position - center‖ ≤ 2 * frequency * length := by
  have horizonNonnegative : 0 ≤ horizon := by linarith
  have continuation := twoDipole_forced_continued_separation frequencyPositive lengthPositive directionNorm
    initialDistanceLarge horizonNonnegative errorNonnegative relativeSmall centerSmall equation externalLipschitz
    inside residualControl firstInitial secondInitial initialProjection initialUpper
  have distanceLarge (time : ℝ) (member : time ∈ Icc 0 horizon) :
      16 * length ≤ ‖firstCenter time - secondCenter time‖ := by
    have control := (continuation time member).2.2.1
    have timeNonnegative := mul_nonneg frequencyPositive.le member.1
    nlinarith
  have midpointDrift := twoDipole_forced_midpoint_drift frequencyPositive lengthPositive directionNorm
    horizonNonnegative errorNonnegative externalNonnegative equation
    (fun time member => (continuation time member).1)
    (fun time member => (continuation time member).2.1) distanceLarge externalControl residualControl
  have endInside : horizon ∈ Icc 0 horizon := ⟨horizonNonnegative, le_rfl⟩
  have centerControl : ‖(firstCenter horizon + secondCenter horizon) / 2 - center‖ ≤
      initialCenterError + 3 * frequency * length * horizon / 16 := by
    have triangle := norm_add_le
      ((firstCenter horizon + secondCenter horizon) / 2 - (firstCenter 0 + secondCenter 0) / 2)
      ((firstCenter 0 + secondCenter 0) / 2 - center)
    rw [sub_add_sub_cancel] at triangle
    have driftSmall := mul_le_mul_of_nonneg_right translationSmall horizonNonnegative
    nlinarith [midpointDrift horizon endInside]
  have firstBounds := dipole_separation_norm_bounds length lengthPositive directionNorm
    (continuation horizon endInside).1
  have secondBounds := dipole_separation_norm_bounds length lengthPositive
    (show ‖-direction‖ = 1 by simpa only [norm_neg] using directionNorm)
    (continuation horizon endInside).2.1
  intro target position member
  have estimate := twoDipole_domain_annular_estimate firstBounds.2 secondBounds.2 centerControl domains target position member
  have lower := (continuation horizon endInside).2.2.1
  have upper := (continuation horizon endInside).2.2.2
  have horizonProductLower := mul_le_mul_of_nonneg_left horizonLower (mul_nonneg frequencyPositive.le lengthPositive.le)
  have horizonProductUpper := mul_le_mul_of_nonneg_left horizonUpper (mul_nonneg frequencyPositive.le lengthPositive.le)
  have initialDistanceProduct := mul_le_mul_of_nonneg_left initialDistanceSmall lengthPositive.le
  have initialDistanceProductNonnegative := mul_nonneg lengthPositive.le (show 0 ≤ initialDistance by linarith)
  constructor <;> nlinarith [estimate.1, estimate.2]

end EulerNonuniqueness.Section7
