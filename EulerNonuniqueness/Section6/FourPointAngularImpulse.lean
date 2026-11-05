import EulerNonuniqueness.Section6.FourPointTranslationControl

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Section6

def fourPointAngularImpulse (positions : FourPointConfiguration) : ℝ :=
  ∑ target : Fin 4, fourPointSign target * ‖positions target‖ ^ 2

theorem fourPointAngularImpulse_translation (positions : FourPointConfiguration) (center : ℂ) :
    fourPointAngularImpulse (positions - fun _ => center) = fourPointAngularImpulse positions -
      2 * (star center * fourPointSignedMoment positions).re := by
  simp [fourPointAngularImpulse, fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

theorem fourPointAngularImpulse_at_arithmeticCenter (positions : FourPointConfiguration) :
    fourPointAngularImpulse (positions - fun _ => fourPointArithmeticCenter positions) =
      2 * (‖(fourPointOddPart positions).1‖ ^ 2 - ‖(fourPointOddPart positions).2‖ ^ 2) := by
  simp [fourPointAngularImpulse, fourPointArithmeticCenter, fourPointOddPart, fourPointSign,
    Fin.sum_univ_succ, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  ring_nf
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem fourPointField_angular_identity (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) :
    (∑ target : Fin 4, (fourPointSign target : ℂ) * star (positions target) *
      fourPointField coefficient positions target) = -2 * Complex.I * (coefficient : ℂ) := by
  let pair := fun first second : Fin 4 =>
    star (positions first) / (star (positions first) - star (positions second)) +
      star (positions second) / (star (positions second) - star (positions first))
  have pairOne (first second : Fin 4) (distinct : second ≠ first) : pair first second = 1 := by
    have denominatorNonzero : star (positions first) - star (positions second) ≠ 0 := by
      simpa only [star_sub] using star_ne_zero.mpr (noncollision first second distinct)
    dsimp only [pair]
    rw [show star (positions second) - star (positions first) =
      -(star (positions first) - star (positions second)) by ring, div_neg, ← sub_eq_add_neg,
      ← sub_div, div_self denominatorNonzero]
  have decomposition : (∑ target : Fin 4, (fourPointSign target : ℂ) * star (positions target) *
      fourPointField coefficient positions target) = Complex.I * (coefficient : ℂ) *
        (pair 0 1 - pair 0 2 - pair 0 3 - pair 1 2 - pair 1 3 + pair 2 3) := by
    simp [fourPointField, fourPointSign, Fin.sum_univ_succ, pair, star_sub]
    ring
  rw [decomposition, pairOne 0 1 (by decide), pairOne 0 2 (by decide), pairOne 0 3 (by decide),
    pairOne 1 2 (by decide), pairOne 1 3 (by decide), pairOne 2 3 (by decide)]
  ring

theorem fourPointAngularImpulse_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) :
    HasDerivAt (fun current => fourPointAngularImpulse (trajectory current)) 0 time := by
  have derivative := HasDerivAt.sum (u := Finset.univ)
    (fun target _ => (equation target).norm_sq.const_mul (fourPointSign target))
  have realIdentity : (∑ target : Fin 4, fourPointSign target *
      (2 * @inner ℝ ℂ _ (trajectory time target) (fourPointField coefficient (trajectory time) target))) = 0 := by
    calc
      _ = 2 * (∑ target : Fin 4, (fourPointSign target : ℂ) * star (trajectory time target) *
          fourPointField coefficient (trajectory time) target).re := by
        rw [Complex.re_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro target _
        rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
        simp [Complex.mul_re, Complex.mul_im, Complex.star_def]
        ring
      _ = 0 := by rw [fourPointField_angular_identity coefficient noncollision]; simp
  simpa only [fourPointAngularImpulse, realIdentity] using derivative

theorem fourPointAngularImpulse_conserved {trajectory : ℝ → FourPointConfiguration} {coefficient : ℝ}
    (noncollision : ∀ time, FourPointNoncollision (trajectory time))
    (equation : ∀ time target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) (firstTime secondTime : ℝ) :
    fourPointAngularImpulse (trajectory firstTime) = fourPointAngularImpulse (trajectory secondTime) := by
  have derivative := fun time => fourPointAngularImpulse_hasDerivAt (noncollision time) (equation time)
  exact is_const_of_deriv_eq_zero (fun time => (derivative time).differentiableAt)
    (fun time => (derivative time).deriv) firstTime secondTime

theorem fourPointAngularImpulse_forced_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => fourPointAngularImpulse (trajectory current))
      (∑ target : Fin 4, fourPointSign target *
        (2 * @inner ℝ ℂ _ (trajectory time target) (forcing target))) time := by
  have derivative := HasDerivAt.sum (u := Finset.univ)
    (fun target _ => (equation target).norm_sq.const_mul (fourPointSign target))
  have internalZero : (∑ target : Fin 4, fourPointSign target *
      (2 * @inner ℝ ℂ _ (trajectory time target) (fourPointField coefficient (trajectory time) target))) = 0 := by
    calc
      _ = 2 * (∑ target : Fin 4, (fourPointSign target : ℂ) * star (trajectory time target) *
          fourPointField coefficient (trajectory time) target).re := by
        rw [Complex.re_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro target _
        rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
        simp [Complex.mul_re, Complex.mul_im, Complex.star_def]
        ring
      _ = 0 := by rw [fourPointField_angular_identity coefficient noncollision]; simp
  simpa only [inner_add_right, mul_add, Finset.sum_add_distrib, internalZero, zero_add,
    fourPointAngularImpulse] using derivative

def fourPointCenteredAngularImpulse (positions : FourPointConfiguration) : ℝ :=
  fourPointAngularImpulse (positions - fun _ => fourPointArithmeticCenter positions)

theorem fourPointCenteredAngularImpulse_forced_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => fourPointCenteredAngularImpulse (trajectory current))
      ((∑ target : Fin 4, fourPointSign target *
          (2 * @inner ℝ ℂ _ (trajectory time target) (forcing target))) -
        2 * (star (fourPointArithmeticCenter (fourPointField coefficient (trajectory time)) +
              fourPointArithmeticCenter forcing) * fourPointSignedMoment (trajectory time) +
            star (fourPointArithmeticCenter (trajectory time)) * fourPointSignedMoment forcing).re) time := by
  have centerDerivative := fourPointArithmeticCenter_forced_hasDerivAt equation
  have conjugateDerivative := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt time centerDerivative
  have productDerivative := conjugateDerivative.mul (fourPointSignedMoment_forced_hasDerivAt equation)
  have realDerivative := Complex.reCLM.hasFDerivAt.comp_hasDerivAt time productDerivative
  have derivative := (fourPointAngularImpulse_forced_hasDerivAt noncollision equation).sub (realDerivative.const_mul 2)
  simpa only [fourPointCenteredAngularImpulse, fourPointAngularImpulse_translation, Complex.star_def] using derivative

theorem fourPointCenteredAngularImpulse_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) :
    HasDerivAt (fun current => fourPointCenteredAngularImpulse (trajectory current))
      (-2 * (star (fourPointArithmeticCenter (fourPointField coefficient (trajectory time))) *
        fourPointSignedMoment (trajectory time)).re) time := by
  have forced := fourPointCenteredAngularImpulse_forced_hasDerivAt (forcing := 0) noncollision
    (fun target => by simpa using equation target)
  have centerZero : fourPointArithmeticCenter (0 : FourPointConfiguration) = 0 := by simp [fourPointArithmeticCenter]
  have momentZero : fourPointSignedMoment (0 : FourPointConfiguration) = 0 := by simp [fourPointSignedMoment]
  simpa only [Pi.zero_apply, inner_zero_right, mul_zero, Finset.sum_const_zero, centerZero, momentZero,
    add_zero, zero_sub, neg_mul] using forced

theorem fourPointShapeImpulse_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) :
    HasDerivAt (fun current => ‖(fourPointOddPart (trajectory current)).1‖ ^ 2 -
      ‖(fourPointOddPart (trajectory current)).2‖ ^ 2)
      (-(star (fourPointArithmeticCenter (fourPointField coefficient (trajectory time))) *
        fourPointSignedMoment (trajectory time)).re) time := by
  have derivative := (fourPointCenteredAngularImpulse_hasDerivAt noncollision equation).div_const 2
  convert derivative using 1
  · funext current
    simp [fourPointCenteredAngularImpulse, fourPointAngularImpulse_at_arithmeticCenter]
  · ring

end EulerNonuniqueness.Section6
