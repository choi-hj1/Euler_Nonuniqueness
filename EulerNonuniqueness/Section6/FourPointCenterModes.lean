import EulerNonuniqueness.Section6.FullFourPointField

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Section6

def fourPointPairCenterMode (positiveCenter negativeCenter : ℂ) : FourPointConfiguration :=
  ![positiveCenter, positiveCenter, negativeCenter, negativeCenter]

theorem fourPointField_translation_invariant (coefficient : ℝ) (positions : FourPointConfiguration) (center : ℂ) :
    fourPointField coefficient (positions + fun _ => center) = fourPointField coefficient positions := by
  funext target
  simp [fourPointField, Pi.add_apply, add_sub_add_right_eq_sub]

theorem fourPointLinearization_translation_zero (coefficient : ℝ) (positions : FourPointConfiguration) (center : ℂ) :
    fourPointLinearization coefficient positions (fun _ => center) = 0 := by
  funext target
  simp [fourPointLinearization]

theorem fourPoint_increment_decomposition (increment : FourPointConfiguration) :
    increment =
      centrallySymmetricFourPoint ((increment 0 - increment 1) / 2) ((increment 2 - increment 3) / 2) +
        fourPointPairCenterMode ((increment 0 + increment 1) / 2) ((increment 2 + increment 3) / 2) := by
  funext target
  fin_cases target <;> simp [centrallySymmetricFourPoint, fourPointPairCenterMode] <;> ring

theorem fourPointLinearization_pairCenterMode (coefficient : ℝ) (positive negative firstCenter secondCenter : ℂ) :
    fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
      (fourPointPairCenterMode firstCenter secondCenter) =
      fun _ => Complex.I * (coefficient : ℂ) * star (firstCenter - secondCenter) *
        (1 / (star positive - star negative) ^ 2 + 1 / (star positive + star negative) ^ 2) := by
  simp only [Complex.star_def]
  funext target
  fin_cases target <;>
    simp [fourPointLinearization, centrallySymmetricFourPoint, fourPointPairCenterMode, fourPointSign,
      Fin.sum_univ_succ] <;> ring

theorem fourPointLinearization_pairCenter_nilpotent (coefficient : ℝ) (positive negative firstCenter secondCenter : ℂ) :
    fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
      (fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
        (fourPointPairCenterMode firstCenter secondCenter)) = 0 := by
  rw [fourPointLinearization_pairCenterMode]
  exact fourPointLinearization_translation_zero _ _ _

theorem fourPointLinearization_central_odd (coefficient : ℝ) (positive negative firstIncrement secondIncrement : ℂ) :
    let linearized := fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
      (centrallySymmetricFourPoint firstIncrement secondIncrement)
    linearized = centrallySymmetricFourPoint (linearized 0) (linearized 2) := by
  dsimp only
  funext target
  fin_cases target <;>
    simp [fourPointLinearization, centrallySymmetricFourPoint, fourPointSign, Fin.sum_univ_succ] <;> ring

theorem fourPointLinearization_add (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) (first second : FourPointConfiguration) :
    fourPointLinearization coefficient positions (first + second) =
      fourPointLinearization coefficient positions first + fourPointLinearization coefficient positions second := by
  rw [← fourPointField_fderiv coefficient noncollision, ← fourPointField_fderiv coefficient noncollision,
    ← fourPointField_fderiv coefficient noncollision]
  exact map_add _ _ _

def fourPointSignedMoment (positions : FourPointConfiguration) : ℂ :=
  ∑ target : Fin 4, (fourPointSign target : ℂ) * positions target

theorem fourPointField_signed_moment_zero (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointSignedMoment (fourPointField coefficient positions) = 0 := by
  let interaction := fun target source : Fin 4 =>
    if source = target then (0 : ℂ) else
      (fourPointSign target : ℂ) * (fourPointSign source : ℂ) / star (positions target - positions source)
  have antisymmetric (target source : Fin 4) : interaction target source = -interaction source target := by
    by_cases same : source = target
    · subst source
      simp [interaction]
    · have reverse : target ≠ source := Ne.symm same
      simp only [interaction, same, reverse, if_false]
      rw [show positions source - positions target = -(positions target - positions source) by ring,
        star_neg, div_neg]
      ring
  have totalNeg : (∑ target : Fin 4, ∑ source : Fin 4, interaction target source) =
      -(∑ target : Fin 4, ∑ source : Fin 4, interaction target source) := by
    calc
      _ = ∑ target : Fin 4, ∑ source : Fin 4, interaction source target := Finset.sum_comm
      _ = ∑ target : Fin 4, ∑ source : Fin 4, -interaction target source := by
        apply Finset.sum_congr rfl
        intro target _
        apply Finset.sum_congr rfl
        intro source _
        exact antisymmetric source target
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have totalZero : (∑ target : Fin 4, ∑ source : Fin 4, interaction target source) = 0 := by
    linear_combination (1 / 2 : ℂ) * totalNeg
  have identity : fourPointSignedMoment (fourPointField coefficient positions) =
      Complex.I * (coefficient : ℂ) * (∑ target : Fin 4, ∑ source : Fin 4, interaction target source) := by
    unfold fourPointSignedMoment fourPointField
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    dsimp [interaction]
    split_ifs <;> ring
  rw [identity, totalZero, mul_zero]

theorem fourPointSignedMoment_hasDerivAt {trajectory : ℝ → FourPointConfiguration} {time coefficient : ℝ}
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) :
    HasDerivAt (fun current => fourPointSignedMoment (trajectory current)) 0 time := by
  have derivative := HasDerivAt.sum (u := Finset.univ)
    (fun target _ => (equation target).const_mul (fourPointSign target : ℂ))
  change HasDerivAt (fun current => fourPointSignedMoment (trajectory current))
    (fourPointSignedMoment (fourPointField coefficient (trajectory time))) time at derivative
  simpa only [fourPointField_signed_moment_zero] using derivative

theorem fourPointSignedMoment_forced_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {time coefficient : ℝ} {forcing : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => fourPointSignedMoment (trajectory current)) (fourPointSignedMoment forcing) time := by
  have derivative := HasDerivAt.sum (u := Finset.univ)
    (fun target _ => (equation target).const_mul (fourPointSign target : ℂ))
  have identity : (∑ target : Fin 4, (fourPointSign target : ℂ) *
      (fourPointField coefficient (trajectory time) target + forcing target)) = fourPointSignedMoment forcing := by
    simp only [mul_add, Finset.sum_add_distrib]
    change fourPointSignedMoment (fourPointField coefficient (trajectory time)) + fourPointSignedMoment forcing = _
    rw [fourPointField_signed_moment_zero, zero_add]
  simpa only [identity] using derivative

theorem fourPointSignedMoment_pairCenterMode (positiveCenter negativeCenter : ℂ) :
    fourPointSignedMoment (fourPointPairCenterMode positiveCenter negativeCenter) =
      2 * (positiveCenter - negativeCenter) := by
  simp [fourPointSignedMoment, fourPointPairCenterMode, fourPointSign, Fin.sum_univ_succ]
  ring

theorem fourPointSignedMoment_central_zero (positive negative : ℂ) :
    fourPointSignedMoment (centrallySymmetricFourPoint positive negative) = 0 := by
  simp [fourPointSignedMoment, centrallySymmetricFourPoint, fourPointSign, Fin.sum_univ_succ]

end EulerNonuniqueness.Section6
