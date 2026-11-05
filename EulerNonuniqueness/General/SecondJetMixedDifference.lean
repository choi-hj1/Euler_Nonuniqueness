import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def complexSecondJetError (function : Domain → Target) (linear : Domain →L[ℂ] Target)
    (bilinear : Domain →L[ℂ] Domain →L[ℂ] Target) (base increment : Domain) : Target :=
  function (base + increment) - function base - linear increment -
    (1 / 2 : ℂ) • bilinear increment increment

theorem secondJet_mixed_difference_identity
    (function : Domain → Target) (linear : Domain →L[ℂ] Target)
    (bilinear : Domain →L[ℂ] Domain →L[ℂ] Target)
    (base first second : Domain) (parameter : ℂ)
    (symmetric : bilinear second first = bilinear first second) :
    function (base + parameter • (first + second)) - function (base + parameter • first) -
        function (base + parameter • second) + function base -
        parameter ^ 2 • bilinear first second =
      complexSecondJetError function linear bilinear base (parameter • (first + second)) -
        complexSecondJetError function linear bilinear base (parameter • first) -
        complexSecondJetError function linear bilinear base (parameter • second) := by
  simp only [complexSecondJetError, smul_add, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, symmetric]
  module

theorem norm_secondJet_mixed_difference_le
    (function : Domain → Target) (linear : Domain →L[ℂ] Target)
    (bilinear : Domain →L[ℂ] Domain →L[ℂ] Target)
    (base first second : Domain) (parameter : ℂ) {constant : ℝ}
    (symmetric : bilinear second first = bilinear first second)
    (sumBound : ‖complexSecondJetError function linear bilinear base (parameter • (first + second))‖ ≤
      constant * ‖parameter • (first + second)‖ ^ 3)
    (firstBound : ‖complexSecondJetError function linear bilinear base (parameter • first)‖ ≤
      constant * ‖parameter • first‖ ^ 3)
    (secondBound : ‖complexSecondJetError function linear bilinear base (parameter • second)‖ ≤
      constant * ‖parameter • second‖ ^ 3) :
    ‖function (base + parameter • (first + second)) - function (base + parameter • first) -
        function (base + parameter • second) + function base -
        parameter ^ 2 • bilinear first second‖ ≤
      constant * ‖parameter‖ ^ 3 * (‖first + second‖ ^ 3 + ‖first‖ ^ 3 + ‖second‖ ^ 3) := by
  rw [secondJet_mixed_difference_identity function linear bilinear base first second parameter symmetric]
  apply (norm_sub_le _ _).trans
  apply (add_le_add_right (norm_sub_le _ _) _).trans
  apply (add_le_add (add_le_add sumBound firstBound) secondBound).trans
  simp only [norm_smul, mul_pow]
  exact le_of_eq (by ring)

theorem norm_secondJet_scaled_mixed_difference_le
    (function : Domain → Target) (linear : Domain →L[ℂ] Target)
    (bilinear : Domain →L[ℂ] Domain →L[ℂ] Target)
    (base first second : Domain) {parameter : ℂ} {constant : ℝ}
    (nonzero : parameter ≠ 0)
    (symmetric : bilinear second first = bilinear first second)
    (sumBound : ‖complexSecondJetError function linear bilinear base (parameter • (first + second))‖ ≤
      constant * ‖parameter • (first + second)‖ ^ 3)
    (firstBound : ‖complexSecondJetError function linear bilinear base (parameter • first)‖ ≤
      constant * ‖parameter • first‖ ^ 3)
    (secondBound : ‖complexSecondJetError function linear bilinear base (parameter • second)‖ ≤
      constant * ‖parameter • second‖ ^ 3) :
    ‖(parameter ^ 2)⁻¹ • (function (base + parameter • (first + second)) -
          function (base + parameter • first) - function (base + parameter • second) + function base) -
        bilinear first second‖ ≤
      constant * ‖parameter‖ * (‖first + second‖ ^ 3 + ‖first‖ ^ 3 + ‖second‖ ^ 3) := by
  have identity : (parameter ^ 2)⁻¹ •
      (function (base + parameter • (first + second)) - function (base + parameter • first) -
        function (base + parameter • second) + function base - parameter ^ 2 • bilinear first second) =
      (parameter ^ 2)⁻¹ • (function (base + parameter • (first + second)) -
        function (base + parameter • first) - function (base + parameter • second) + function base) -
        bilinear first second := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 nonzero), one_smul]
  rw [← identity, norm_smul, norm_inv, norm_pow]
  apply (mul_le_mul_of_nonneg_left
    (norm_secondJet_mixed_difference_le function linear bilinear base first second parameter
      symmetric sumBound firstBound secondBound) (by positivity)).trans
  have normNonzero : ‖parameter‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  apply le_of_eq
  field_simp
  <;> ring

end

end EulerNonuniqueness.General
