import EulerNonuniqueness.Section6.SeparatingStrain

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace EulerNonuniqueness.Section6

abbrev FourPointConfiguration := Fin 4 → ℂ

def fourPointSign (index : Fin 4) : ℝ := if index.val < 2 then 1 else -1

def FourPointNoncollision (positions : FourPointConfiguration) : Prop :=
  ∀ target source, source ≠ target → positions target - positions source ≠ 0

def fourPointField (coefficient : ℝ) (positions : FourPointConfiguration) : FourPointConfiguration :=
  fun target => Complex.I * (coefficient : ℂ) * ∑ source : Fin 4,
    if source = target then 0 else (fourPointSign source : ℂ) / star (positions target - positions source)

def fourPointLinearization (coefficient : ℝ) (positions increment : FourPointConfiguration) : FourPointConfiguration :=
  fun target => -Complex.I * (coefficient : ℂ) * ∑ source : Fin 4,
    if source = target then 0 else
      (fourPointSign source : ℂ) * star (increment target - increment source) /
        star (positions target - positions source) ^ 2

theorem fourPointField_contDiffAt (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) : ContDiffAt ℝ 2 (fourPointField coefficient) positions := by
  apply contDiffAt_pi.mpr
  intro target
  unfold fourPointField
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro source _
  by_cases same : source = target
  · simp only [same, if_true]
    exact contDiffAt_const
  · simp only [same, if_false]
    have difference : ContDiffAt ℝ 2
        (fun current : FourPointConfiguration => current target - current source) positions := by fun_prop
    have conjugate : ContDiffAt ℝ 2
        (fun current : FourPointConfiguration => star (current target - current source)) positions := by
      exact Complex.conjCLE.contDiff.contDiffAt.comp positions difference
    simpa only [div_eq_mul_inv] using
      contDiffAt_const.mul (conjugate.inv (star_ne_zero.mpr (noncollision target source same)))

theorem fourPointField_directional_hasDerivAt (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) (increment : FourPointConfiguration) :
    HasDerivAt (fun time : ℝ => fourPointField coefficient (positions + time • increment))
      (fourPointLinearization coefficient positions increment) 0 := by
  apply hasDerivAt_pi.mpr
  intro target
  have derivative : ∀ source ∈ (Finset.univ : Finset (Fin 4)), HasDerivAt
      (fun time : ℝ => if source = target then (0 : ℂ) else
        (fourPointSign source : ℂ) / star ((positions + time • increment) target - (positions + time • increment) source))
      (if source = target then (0 : ℂ) else
        -((fourPointSign source : ℂ) * star (increment target - increment source)) /
          star (positions target - positions source) ^ 2) 0 := by
    intro source _
    by_cases same : source = target
    · simpa only [same, if_true] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simp only [same, if_false]
      have targetDerivative : HasDerivAt
          (fun time : ℝ => positions target + (time : ℂ) * increment target) (increment target) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (increment target)).const_add (positions target)
      have sourceDerivative : HasDerivAt
          (fun time : ℝ => positions source + (time : ℂ) * increment source) (increment source) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (increment source)).const_add (positions source)
      have conjugate := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (targetDerivative.sub sourceDerivative)
      have quotient := (hasDerivAt_const (0 : ℝ) (fourPointSign source : ℂ)).div conjugate
        (by simpa using star_ne_zero.mpr (noncollision target source same))
      simpa using quotient
  have summed := (HasDerivAt.sum derivative).const_mul (Complex.I * (coefficient : ℂ))
  convert summed using 1
  dsimp [fourPointLinearization]
  have sumIdentity : (∑ source : Fin 4, if source = target then (0 : ℂ) else
      -((fourPointSign source : ℂ) * star (increment target - increment source)) /
        star (positions target - positions source) ^ 2) =
      -(∑ source : Fin 4, if source = target then (0 : ℂ) else
        (fourPointSign source : ℂ) * star (increment target - increment source) /
          star (positions target - positions source) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro source _
    split_ifs <;> ring
  simp only [Complex.star_def] at sumIdentity
  rw [sumIdentity]
  ring

theorem fourPointField_fderiv (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) (increment : FourPointConfiguration) :
    fderiv ℝ (fourPointField coefficient) positions increment =
      fourPointLinearization coefficient positions increment := by
  have line : HasDerivAt (fun time : ℝ => positions + time • increment) increment 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const increment).const_add positions
  have differentiable : DifferentiableAt ℝ (fourPointField coefficient) positions :=
    (fourPointField_contDiffAt coefficient noncollision).differentiableAt (by norm_num)
  have chain := HasFDerivAt.comp_hasDerivAt
    (l := fourPointField coefficient) (l' := fderiv ℝ (fourPointField coefficient) positions) 0
    (by simpa only [zero_smul, add_zero] using differentiable.hasFDerivAt) line
  exact chain.unique (fourPointField_directional_hasDerivAt coefficient noncollision increment)

theorem fourPointField_scaling (coefficient : ℝ) (positions : FourPointConfiguration) :
    fourPointField coefficient positions = coefficient • fourPointField 1 positions := by
  funext target
  simp only [fourPointField, Pi.smul_apply, Complex.ofReal_one, mul_one, Complex.real_smul]
  ring

theorem fourPointLinearization_scaling (coefficient : ℝ) (positions increment : FourPointConfiguration) :
    fourPointLinearization coefficient positions increment = coefficient • fourPointLinearization 1 positions increment := by
  funext target
  simp only [fourPointLinearization, Pi.smul_apply, Complex.ofReal_one, mul_one, Complex.real_smul]
  ring

theorem fourPointField_quadratic_remainder {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ increment : FourPointConfiguration,
      ‖increment‖ < radius →
      ‖fourPointField coefficient (positions + increment) - fourPointField coefficient positions -
        fourPointLinearization coefficient positions increment‖ ≤
      bound * |coefficient| * ‖increment‖ ^ 2 := by
  have smooth : ContDiffAt ℝ 2
      (fun increment : FourPointConfiguration => fourPointField 1 (positions + increment)) 0 := by
    apply ContDiffAt.comp (f := fun increment : FourPointConfiguration => positions + increment)
      (g := fourPointField 1) 0
    · simpa only [add_zero] using fourPointField_contDiffAt 1 noncollision
    · fun_prop
  have fieldDerivative : HasFDerivAt (fourPointField 1) (fderiv ℝ (fourPointField 1) positions) positions :=
    ((fourPointField_contDiffAt 1 noncollision).differentiableAt (by norm_num)).hasFDerivAt
  have derivative : HasFDerivAt
      (fun increment : FourPointConfiguration => fourPointField 1 (positions + increment))
      (fderiv ℝ (fourPointField 1) positions) 0 := by
    have translation : HasFDerivAt (fun increment : FourPointConfiguration => positions + increment)
        (ContinuousLinearMap.id ℝ FourPointConfiguration) 0 :=
      (hasFDerivAt_id (𝕜 := ℝ) (0 : FourPointConfiguration)).const_add positions
    have outer : HasFDerivAt (fourPointField 1) (fderiv ℝ (fourPointField 1) positions)
        (positions + (0 : FourPointConfiguration)) := by simpa only [add_zero] using fieldDerivative
    simpa only [ContinuousLinearMap.comp_id] using outer.comp 0 translation
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ := contDiffAt_quadratic_remainder smooth
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient increment incrementSmall
  have estimate := estimate increment incrementSmall
  rw [derivative.fderiv, fourPointField_fderiv 1 noncollision] at estimate
  simp only [add_zero] at estimate
  rw [fourPointField_scaling coefficient (positions + increment), fourPointField_scaling coefficient positions,
    fourPointLinearization_scaling coefficient positions increment, ← smul_sub, ← smul_sub, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |coefficient| * (bound * ‖increment‖ ^ 2) := mul_le_mul_of_nonneg_left estimate (abs_nonneg _)
    _ = _ := by ring

def centrallySymmetricFourPoint (positive negative : ℂ) : FourPointConfiguration :=
  ![positive, -positive, negative, -negative]

theorem fourPointField_central_embedding (coefficient : ℝ) {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (differenceNonzero : positive - negative ≠ 0) (sumNonzero : positive + negative ≠ 0) :
    fourPointField coefficient (centrallySymmetricFourPoint positive negative) =
      centrallySymmetricFourPoint (positivePointVelocity coefficient positive negative)
        (negativePointVelocity coefficient positive negative) := by
  have positiveStarNonzero := star_ne_zero.mpr positiveNonzero
  have negativeStarNonzero := star_ne_zero.mpr negativeNonzero
  have differenceStarNonzero : star positive - star negative ≠ 0 := by
    simpa only [star_sub] using star_ne_zero.mpr differenceNonzero
  have sumStarNonzero : star positive + star negative ≠ 0 := by
    simpa only [star_add] using star_ne_zero.mpr sumNonzero
  have squaresStarNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero sumStarNonzero differenceStarNonzero
  have reverseDifference : star negative - star positive ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp differenceStarNonzero))
  have reverseSum : star negative + star positive ≠ 0 := by simpa only [add_comm] using sumStarNonzero
  have negativeSum : -star positive - star negative ≠ 0 := by
    intro zero
    apply sumStarNonzero
    linear_combination -zero
  have negativeDifference : -star positive + star negative ≠ 0 := by
    intro zero
    apply differenceStarNonzero
    linear_combination -zero
  have reverseNegativeSum : -star negative - star positive ≠ 0 := by
    intro zero
    apply sumStarNonzero
    linear_combination -zero
  have reverseNegativeDifference : -star negative + star positive ≠ 0 := by
    simpa only [add_comm] using differenceStarNonzero
  simp only [Complex.star_def] at *
  funext target
  fin_cases target <;>
    simp [fourPointField, centrallySymmetricFourPoint, fourPointSign, Fin.sum_univ_succ,
      positivePointVelocity, negativePointVelocity] <;>
    field_simp [mul_ne_zero_iff, pow_ne_zero_iff, positiveStarNonzero, negativeStarNonzero,
      differenceStarNonzero, sumStarNonzero, squaresStarNonzero, reverseDifference,
      negativeSum, negativeDifference, reverseNegativeSum, reverseNegativeDifference, reverseSum] <;>
    first
    | (ring; done)
    | linear_combination -Complex.I * (coefficient : ℂ) *
        ((starRingEnd ℂ) positive ^ 2 - (starRingEnd ℂ) negative ^ 2) ^ 2 *
          (mul_inv_cancel₀ positiveStarNonzero)
    | linear_combination -Complex.I * (coefficient : ℂ) *
        ((starRingEnd ℂ) positive ^ 2 - (starRingEnd ℂ) negative ^ 2) ^ 2 *
          (mul_inv_cancel₀ negativeStarNonzero)

theorem centrallySymmetricFourPoint_noncollision {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (differenceNonzero : positive - negative ≠ 0) (sumNonzero : positive + negative ≠ 0) :
    FourPointNoncollision (centrallySymmetricFourPoint positive negative) := by
  intro target source different
  fin_cases target <;> fin_cases source <;> simp_all [centrallySymmetricFourPoint] <;>
    intro zero <;>
    first
    | (apply positiveNonzero; linear_combination -(1 / 2 : ℂ) * zero)
    | (apply negativeNonzero; linear_combination -(1 / 2 : ℂ) * zero)
    | (apply differenceNonzero; linear_combination zero)
    | (apply differenceNonzero; linear_combination -zero)
    | (apply sumNonzero; linear_combination zero)
    | (apply sumNonzero; linear_combination -zero)

end EulerNonuniqueness.Section6
