import EulerNonuniqueness.Section6.PairedDipoleHessian
import EulerNonuniqueness.Section6.PointSourceDifferentiation

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

def fourPointExternalPointHessian (coefficient : ℝ) (positions : FourPointConfiguration) (location : ℂ) : ℂ :=
  Complex.I * (coefficient : ℂ) * star (fourPointCauchyHessian positions location)

theorem fourPointCauchyHessian_conjugate (positions : FourPointConfiguration) (location : ℂ) :
    star (fourPointCauchyHessian positions location) =
      fourPointCauchyHessian (fun target => star (positions target)) (star location) := by
  simp [fourPointCauchyHessian, star_sum, star_div₀, star_sub]

theorem fourPointExternalPointStrain_hasFDerivAt (coefficient : ℝ) (positions : FourPointConfiguration)
    {location : ℂ} (noncollision : ∀ target, location - positions target ≠ 0) :
    HasFDerivAt (fourPointExternalPointStrain coefficient positions)
      (fourPointExternalPointHessian coefficient positions location •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) location := by
  have complexDerivative := fourPointCauchyStrain_hasDerivAt (fun target => star (positions target))
    (location := star location) (fun target => by simpa only [star_sub] using star_ne_zero.mpr (noncollision target))
  have outer := complexDerivative.const_mul (Complex.I * (coefficient : ℂ))
  have conjugate : HasFDerivAt (fun current : ℂ => star current)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) location := Complex.conjCLE.hasFDerivAt
  have derivative := outer.comp_hasFDerivAt location conjugate
  convert derivative using 1
  · funext current
    simp only [fourPointExternalPointStrain, fourPointCauchyStrain_conjugate, Function.comp_apply]
  · simp only [fourPointExternalPointHessian, fourPointCauchyHessian_conjugate]

theorem norm_antilinear_conjugation (coefficient : ℂ) :
    ‖coefficient • (Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ = ‖coefficient‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro increment
    change ‖coefficient * star increment‖ ≤ ‖coefficient‖ * ‖increment‖
    rw [norm_mul, norm_star]
  · have estimate := (coefficient • (Complex.conjCLE : ℂ →L[ℝ] ℂ)).le_opNorm (1 : ℂ)
    change ‖coefficient * star (1 : ℂ)‖ ≤ ‖coefficient • (Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ * ‖(1 : ℂ)‖ at estimate
    simpa only [star_one, mul_one, norm_one] using estimate

theorem fourPointExternalPointVelocity_fderiv_lipschitz (coefficient : ℝ) (positions : FourPointConfiguration)
    {region : Set ℂ} {bound : ℝ≥0} (convex : Convex ℝ region)
    (noncollision : ∀ location ∈ region, ∀ target, location - positions target ≠ 0)
    (hessianBound : ∀ location ∈ region, ‖fourPointExternalPointHessian coefficient positions location‖ ≤ bound) :
    LipschitzOnWith bound (fderiv ℝ (fourPointExternalPointVelocity coefficient positions)) region := by
  have derivative (location : ℂ) (member : location ∈ region) :=
    (fourPointExternalPointStrain_hasFDerivAt coefficient positions (noncollision location member)).hasFDerivWithinAt (s := region)
  have derivativeBound (location : ℂ) (member : location ∈ region) :
      ‖fourPointExternalPointHessian coefficient positions location • (Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ bound := by
    rw [norm_antilinear_conjugation]
    exact hessianBound location member
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstInside second secondInside
  rw [(fourPointExternalPointVelocity_hasFDerivAt coefficient positions (noncollision first firstInside)).fderiv,
    (fourPointExternalPointVelocity_hasFDerivAt coefficient positions (noncollision second secondInside)).fderiv,
    ← sub_smul, norm_antilinear_conjugation]
  exact convex.norm_image_sub_le_of_norm_hasFDerivWithin_le derivative derivativeBound secondInside firstInside

theorem twoDipole_physical_hessian_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointExternalPointHessian coefficient
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location‖ ≤
      |coefficient| * (6 * ‖firstSeparation + secondSeparation‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 +
        12 * ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation)‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 5 +
        9344 * ‖firstCenter - secondCenter‖ ^ 2 * length /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 6) := by
  let displacement := location - (firstCenter + secondCenter) / 2
  let moment := (firstCenter - secondCenter) * (firstSeparation - secondSeparation)
  let field := fourPointCauchyHessian
    (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location
  have estimate := twoDipole_CauchyHessian_far_field lengthPositive firstBound secondBound separated far
  have identity : field = 6 * (firstSeparation + secondSeparation) / displacement ^ 4 +
      12 * moment / displacement ^ 5 +
      (field - 6 * (firstSeparation + secondSeparation) / displacement ^ 4 - 12 * moment / displacement ^ 5) := by ring
  have fieldBound : ‖field‖ ≤ 6 * ‖firstSeparation + secondSeparation‖ / ‖displacement‖ ^ 4 +
      12 * ‖moment‖ / ‖displacement‖ ^ 5 + 9344 * ‖firstCenter - secondCenter‖ ^ 2 * length / ‖displacement‖ ^ 6 := by
    conv_lhs => rw [identity]
    apply (norm_add_le _ _).trans
    apply add_le_add _ estimate
    apply (norm_add_le _ _).trans
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, le_refl]
  unfold fourPointExternalPointHessian
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
  exact mul_le_mul_of_nonneg_left fieldBound (abs_nonneg coefficient)

theorem twoDipole_physical_hessian_moment_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation location : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (separated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖fourPointExternalPointHessian coefficient
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location‖ ≤
      |coefficient| * (6 * ‖firstSeparation + secondSeparation‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 +
        4720 * ‖firstCenter - secondCenter‖ * length /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 5) := by
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
  have quadrupoleControl : 12 * ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation)‖ / distance ^ 5 ≤
      48 * radius * length / distance ^ 5 := by
    calc
      _ ≤ 12 * (4 * radius * length) / distance ^ 5 := by gcongr
      _ = _ := by ring
  have remainderControl : 9344 * radius ^ 2 * length / distance ^ 6 ≤ 4672 * radius * length / distance ^ 5 := by
    calc
      _ = (9344 * radius * length / distance ^ 5) * (radius / distance) := by
        field_simp [distancePositive.ne']
        ring
      _ ≤ (9344 * radius * length / distance ^ 5) * (1 / 2) :=
        mul_le_mul_of_nonneg_left ratioBound (by dsimp [radius]; positivity)
      _ = _ := by ring
  apply (twoDipole_physical_hessian_bound coefficient lengthPositive firstBound secondBound separated far).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg coefficient)
  have estimate := add_le_add_left (add_le_add quadrupoleControl remainderControl)
    (6 * ‖firstSeparation + secondSeparation‖ / distance ^ 4)
  convert estimate using 1 <;> dsimp [radius, distance] <;> ring

end EulerNonuniqueness.Section6
