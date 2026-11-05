import EulerNonuniqueness.Section6.UniformPointSourceHessian
import EulerNonuniqueness.Section6.SourceMomentStrainError

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_physical_strain_moment_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointExternalPointStrain coefficient
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location‖ ≤
      |coefficient| * (2 * ‖firstSeparation + secondSeparation‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 3 +
        364 * ‖firstCenter - secondCenter‖ * length /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 4) := by
  let distance := ‖location - (firstCenter + secondCenter) / 2‖
  let radius := ‖firstCenter - secondCenter‖
  have distancePositive : 0 < distance := by dsimp [distance]; nlinarith
  have ratioBound : radius / distance ≤ 1 / 2 :=
    (div_le_iff₀ distancePositive).mpr (by dsimp [radius, distance]; linarith)
  have momentBound : ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation)‖ ≤ 4 * radius * length := by
    rw [norm_mul]
    have separationBound : ‖firstSeparation - secondSeparation‖ ≤ 4 * length :=
      (norm_sub_le _ _).trans (by linarith)
    calc
      _ ≤ radius * (4 * length) := mul_le_mul_of_nonneg_left separationBound (norm_nonneg _)
      _ = _ := by ring
  have quadrupoleControl : 3 * |coefficient| * ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation)‖ / distance ^ 4 ≤
      12 * |coefficient| * radius * length / distance ^ 4 := by
    calc
      _ ≤ 3 * |coefficient| * (4 * radius * length) / distance ^ 4 := by gcongr
      _ = _ := by ring
  have remainderControl : 704 * |coefficient| * radius ^ 2 * length / distance ^ 5 ≤
      352 * |coefficient| * radius * length / distance ^ 4 := by
    calc
      _ = (704 * |coefficient| * radius * length / distance ^ 4) * (radius / distance) := by
        field_simp [distancePositive.ne']
        ring
      _ ≤ (704 * |coefficient| * radius * length / distance ^ 4) * (1 / 2) :=
        mul_le_mul_of_nonneg_left ratioBound (by dsimp [radius]; positivity)
      _ = _ := by ring
  have estimate := twoDipole_physical_strain_moment_error coefficient lengthPositive firstBound secondBound separated far 0
  simp only [star_zero, mul_zero, zero_div, sub_zero] at estimate
  apply estimate.trans
  have control := add_le_add_left (add_le_add quadrupoleControl remainderControl)
    (2 * |coefficient| * ‖firstSeparation + secondSeparation‖ / distance ^ 3)
  convert control using 1 <;> dsimp [radius, distance] <;> ring

theorem twoDipole_source_lipschitz_on_ball (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation receiverCenter : ℂ}
    {length receiverRadius : ℝ} {bound : ℝ≥0}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : 4 * ‖firstCenter - secondCenter‖ ≤ ‖receiverCenter - (firstCenter + secondCenter) / 2‖)
    (receiverSmall : receiverRadius ≤ ‖receiverCenter - (firstCenter + secondCenter) / 2‖ / 2)
    (boundLarge : |coefficient| * (16 * ‖firstSeparation + secondSeparation‖ /
        ‖receiverCenter - (firstCenter + secondCenter) / 2‖ ^ 3 +
      5824 * ‖firstCenter - secondCenter‖ * length /
        ‖receiverCenter - (firstCenter + secondCenter) / 2‖ ^ 4) ≤ bound) :
    LipschitzOnWith bound (fourPointExternalPointVelocity coefficient
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation))
      (Metric.closedBall receiverCenter receiverRadius) := by
  let positions := twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation
  have geometry := twoDipole_receiver_ball_separation lengthPositive firstBound secondBound separated far receiverSmall
  have derivative (location : ℂ) (member : location ∈ Metric.closedBall receiverCenter receiverRadius) :=
    (fourPointExternalPointVelocity_hasFDerivAt coefficient positions (geometry location member).2.2).hasFDerivWithinAt
      (s := Metric.closedBall receiverCenter receiverRadius)
  have derivativeBound (location : ℂ) (member : location ∈ Metric.closedBall receiverCenter receiverRadius) :
      ‖fourPointExternalPointStrain coefficient positions location • (Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ bound := by
    rw [norm_antilinear_conjugation]
    have localGeometry := geometry location member
    have estimate := twoDipole_physical_strain_moment_bound coefficient lengthPositive firstBound secondBound separated localGeometry.2.1
    apply estimate.trans
    apply le_trans _ boundLarge
    let distance := ‖receiverCenter - (firstCenter + secondCenter) / 2‖
    have distancePositive : 0 < distance := by dsimp [distance]; nlinarith
    have halfPositive : 0 < distance / 2 := by positivity
    have lower := localGeometry.1
    have firstControl : 2 * ‖firstSeparation + secondSeparation‖ /
        ‖location - (firstCenter + secondCenter) / 2‖ ^ 3 ≤
        16 * ‖firstSeparation + secondSeparation‖ / distance ^ 3 := by
      calc
        _ ≤ 2 * ‖firstSeparation + secondSeparation‖ / (distance / 2) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos halfPositive 3) (pow_le_pow_left₀ halfPositive.le lower 3)
        _ = _ := by field_simp [distancePositive.ne']; ring
    have secondControl : 364 * ‖firstCenter - secondCenter‖ * length /
        ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 ≤
        5824 * ‖firstCenter - secondCenter‖ * length / distance ^ 4 := by
      calc
        _ ≤ 364 * ‖firstCenter - secondCenter‖ * length / (distance / 2) ^ 4 :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos halfPositive 4) (pow_le_pow_left₀ halfPositive.le lower 4)
        _ = _ := by field_simp [distancePositive.ne']; ring
    exact mul_le_mul_of_nonneg_left (add_le_add firstControl secondControl) (abs_nonneg coefficient)
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstInside second secondInside
  exact (convex_closedBall receiverCenter receiverRadius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    derivative derivativeBound secondInside firstInside

end EulerNonuniqueness.Section6
