import EulerNonuniqueness.Section6.PhaseStraightening
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

def positivePointVelocity (coefficient : ℝ) (positive negative : ℂ) : ℂ :=
  -Complex.I * (coefficient : ℂ) * (3 * star positive ^ 2 + star negative ^ 2) /
    (2 * star positive * (star positive ^ 2 - star negative ^ 2))

def negativePointVelocity (coefficient : ℝ) (positive negative : ℂ) : ℂ :=
  -Complex.I * (coefficient : ℂ) * (star positive ^ 2 + 3 * star negative ^ 2) /
    (2 * star negative * (star positive ^ 2 - star negative ^ 2))

theorem point_logarithmic_velocities (coefficient : ℝ) {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (squaresNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0) :
    positivePointVelocity coefficient positive negative / positive =
      -Complex.I * (coefficient : ℂ) / (2 * (positive * star positive)) *
        ((3 + (star negative / star positive) ^ 2) / (1 - (star negative / star positive) ^ 2)) ∧
    negativePointVelocity coefficient positive negative / negative =
      -Complex.I * (coefficient : ℂ) / (2 * (negative * star negative)) *
        ((1 + 3 * (star negative / star positive) ^ 2) / (1 - (star negative / star positive) ^ 2)) := by
  have positiveStarNonzero : star positive ≠ 0 := star_ne_zero.mpr positiveNonzero
  have negativeStarNonzero : star negative ≠ 0 := star_ne_zero.mpr negativeNonzero
  have shapeDenominator : 1 - (star negative / star positive) ^ 2 ≠ 0 := by
    intro equality
    apply squaresNonzero
    have quotientEquality : star negative ^ 2 / star positive ^ 2 = 1 := by
      rw [← div_pow]
      exact (sub_eq_zero.mp equality).symm
    have squaresEquality := (div_eq_iff (pow_ne_zero 2 positiveStarNonzero)).mp quotientEquality
    exact sub_eq_zero.mpr (by simpa only [one_mul] using squaresEquality.symm)
  constructor <;> simp only [positivePointVelocity, negativePointVelocity] <;>
    field_simp [positiveNonzero, negativeNonzero, positiveStarNonzero, negativeStarNonzero,
      squaresNonzero, shapeDenominator] <;> ring

def shapeConjugateRatio (ratio phase : ℝ) : ℂ :=
  ⟨ratio * Real.cos phase, -ratio * Real.sin phase⟩

def positiveShapeLogVelocity (frequency ratio phase : ℝ) : ℂ :=
  -Complex.I * (frequency : ℂ) * (1 - (ratio : ℂ)) / 2 *
    ((3 + shapeConjugateRatio ratio phase) / (1 - shapeConjugateRatio ratio phase))

def negativeShapeLogVelocity (frequency ratio phase : ℝ) : ℂ :=
  -Complex.I * (frequency : ℂ) * (1 - (ratio : ℂ)) / (2 * (ratio : ℂ)) *
    ((1 + 3 * shapeConjugateRatio ratio phase) / (1 - shapeConjugateRatio ratio phase))

theorem shape_denominator_positive {ratio phase : ℝ} (ratioPositive : 0 < ratio) (belowOne : ratio < 1) :
    0 < 1 + ratio ^ 2 - 2 * ratio * Real.cos phase := by
  have cosineBound := Real.cos_le_one phase
  have nonnegative : 0 ≤ 2 * ratio * (1 - Real.cos phase) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr cosineBound)
  nlinarith [sq_pos_of_pos (sub_pos.mpr belowOne)]

theorem shapeConjugateRatio_denominator_normSq (ratio phase : ℝ) :
    Complex.normSq (1 - shapeConjugateRatio ratio phase) =
      1 + ratio ^ 2 - 2 * ratio * Real.cos phase := by
  simp only [shapeConjugateRatio, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im]
  linear_combination ratio ^ 2 * Real.sin_sq_add_cos_sq phase

theorem shape_logarithmic_velocity_components (frequency : ℝ) {ratio phase : ℝ}
    (ratioPositive : 0 < ratio) (belowOne : ratio < 1) :
    2 * ratio * (negativeShapeLogVelocity frequency ratio phase - positiveShapeLogVelocity frequency ratio phase).re =
      radialVelocity frequency ratio phase ∧
    2 * (negativeShapeLogVelocity frequency ratio phase - positiveShapeLogVelocity frequency ratio phase).im =
      shapeAngleVelocity frequency ratio phase ∧
    (positiveShapeLogVelocity frequency ratio phase).im = rotationVelocity frequency ratio phase := by
  have denominatorPositive := shape_denominator_positive (phase := phase) ratioPositive belowOne
  have normSqIdentity := shapeConjugateRatio_denominator_normSq ratio phase
  have ratioNonzero := ratioPositive.ne'
  have denominatorNonzero := denominatorPositive.ne'
  simp only [positiveShapeLogVelocity, negativeShapeLogVelocity, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  rw [normSqIdentity]
  simp [shapeConjugateRatio, Complex.normSq_apply]
  constructor
  · unfold radialVelocity
    field_simp
    ring
  · constructor
    · unfold shapeAngleVelocity
      field_simp
      ring_nf
      simp only [Real.sin_sq]
      ring
    · unfold rotationVelocity
      field_simp
      ring_nf
      simp only [Real.sin_sq]
      ring

theorem point_logarithmic_velocities_in_shape (coefficient : ℝ) {positive negative : ℂ} {ratio phase : ℝ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (squaresNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0)
    (ratioPositive : 0 < ratio) (belowOne : ratio < 1)
    (ratioIdentity : ratio = ‖negative‖ ^ 2 / ‖positive‖ ^ 2)
    (phaseIdentity : (star negative / star positive) ^ 2 = shapeConjugateRatio ratio phase) :
    positivePointVelocity coefficient positive negative / positive =
      positiveShapeLogVelocity (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) ratio phase ∧
    negativePointVelocity coefficient positive negative / negative =
      negativeShapeLogVelocity (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) ratio phase := by
  have positiveNormNonzero : ‖positive‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr positiveNonzero)
  have negativeNormNonzero : ‖negative‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr negativeNonzero)
  have negativeNormIdentity : ‖negative‖ ^ 2 = ratio * ‖positive‖ ^ 2 :=
    ((eq_div_iff positiveNormNonzero).mp ratioIdentity).symm
  have impulseNonzero : ‖positive‖ ^ 2 - ‖negative‖ ^ 2 ≠ 0 := by
    rw [negativeNormIdentity]
    rw [show ‖positive‖ ^ 2 - ratio * ‖positive‖ ^ 2 = ‖positive‖ ^ 2 * (1 - ratio) by ring]
    exact mul_ne_zero positiveNormNonzero (sub_pos.mpr belowOne).ne'
  have positiveProduct : positive * star positive = (‖positive‖ ^ 2 : ℝ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj positive
  have negativeProduct : negative * star negative = (‖negative‖ ^ 2 : ℝ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj negative
  have impulseFactor : ‖positive‖ ^ 2 - ‖negative‖ ^ 2 = ‖positive‖ ^ 2 * (1 - ratio) := by
    rw [negativeNormIdentity]
    ring
  have positiveScalar : coefficient / (2 * ‖positive‖ ^ 2) =
      (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) * (1 - ratio) / 2 := by
    rw [impulseFactor]
    field_simp [positiveNormNonzero, (sub_pos.mpr belowOne).ne']
    ring
  have negativeScalar : coefficient / (2 * ‖negative‖ ^ 2) =
      (coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2)) * (1 - ratio) / (2 * ratio) := by
    rw [impulseFactor, negativeNormIdentity]
    field_simp [positiveNormNonzero, (sub_pos.mpr belowOne).ne', ratioPositive.ne']
    ring
  have positivePrefactor : -Complex.I * (coefficient : ℂ) / (2 * (positive * star positive)) =
      -Complex.I * ((coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2) : ℝ) : ℂ) * (1 - (ratio : ℂ)) / 2 := by
    rw [positiveProduct]
    calc
      _ = -Complex.I * ((coefficient / (2 * ‖positive‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
      _ = _ := by rw [positiveScalar]; push_cast; ring
  have negativePrefactor : -Complex.I * (coefficient : ℂ) / (2 * (negative * star negative)) =
      -Complex.I * ((coefficient / (‖positive‖ ^ 2 - ‖negative‖ ^ 2) : ℝ) : ℂ) *
        (1 - (ratio : ℂ)) / (2 * (ratio : ℂ)) := by
    rw [negativeProduct]
    calc
      _ = -Complex.I * ((coefficient / (2 * ‖negative‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
      _ = _ := by rw [negativeScalar]; push_cast; ring
  have logarithmic := point_logarithmic_velocities coefficient positiveNonzero negativeNonzero squaresNonzero
  constructor
  · rw [logarithmic.1, positivePrefactor, phaseIdentity]
    rfl
  · rw [logarithmic.2, negativePrefactor, phaseIdentity]
    rfl

theorem shape_logarithmic_radial_balance (frequency : ℝ) {ratio phase : ℝ}
    (ratioPositive : 0 < ratio) (belowOne : ratio < 1) :
    (positiveShapeLogVelocity frequency ratio phase).re =
      ratio * (negativeShapeLogVelocity frequency ratio phase).re := by
  have denominatorNonzero := (shape_denominator_positive (phase := phase) ratioPositive belowOne).ne'
  simp only [positiveShapeLogVelocity, negativeShapeLogVelocity, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  rw [shapeConjugateRatio_denominator_normSq]
  simp [shapeConjugateRatio, Complex.normSq_apply]
  field_simp
  ring

theorem point_shape_phase_identity (positive negative : ℂ) :
    (star negative / star positive) ^ 2 =
      shapeConjugateRatio (‖negative‖ ^ 2 / ‖positive‖ ^ 2)
        (Complex.arg ((negative / positive) ^ 2)) := by
  have normIdentity : ‖(negative / positive) ^ 2‖ = ‖negative‖ ^ 2 / ‖positive‖ ^ 2 := by
    rw [norm_pow, norm_div, div_pow]
  have conjugateIdentity : (star negative / star positive) ^ 2 = star ((negative / positive) ^ 2) := by
    simp only [star_pow, star_div₀]
  rw [conjugateIdentity]
  apply Complex.ext
  · change ((negative / positive) ^ 2).re = _
    rw [← normIdentity]
    exact (Complex.norm_mul_cos_arg ((negative / positive) ^ 2)).symm
  · change -((negative / positive) ^ 2).im = _
    rw [← normIdentity]
    simpa only [shapeConjugateRatio, neg_mul] using
      congrArg Neg.neg (Complex.norm_mul_sin_arg ((negative / positive) ^ 2)).symm

theorem real_inner_logarithmic_velocity {point velocity : ℂ} (nonzero : point ≠ 0) :
    @inner ℝ ℂ _ point velocity = ‖point‖ ^ 2 * (velocity / point).re := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.div_re]
  rw [← Complex.normSq_eq_norm_sq]
  have normNonzero : Complex.normSq point ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero)
  field_simp [normNonzero]

theorem norm_ratio_hasDerivAt {positive negative : ℝ → ℂ} {positiveVelocity negativeVelocity : ℂ}
    {time : ℝ} (positiveDerivative : HasDerivAt positive positiveVelocity time)
    (negativeDerivative : HasDerivAt negative negativeVelocity time)
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0) :
    HasDerivAt (fun t => ‖negative t‖ ^ 2 / ‖positive t‖ ^ 2)
      (2 * (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2) *
        (negativeVelocity / negative time - positiveVelocity / positive time).re) time := by
  have derivative := negativeDerivative.norm_sq.div positiveDerivative.norm_sq
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr positiveNonzero))
  convert derivative using 1
  rw [real_inner_logarithmic_velocity positiveNonzero,
    real_inner_logarithmic_velocity negativeNonzero, Complex.sub_re]
  field_simp
  ring

theorem four_point_impulse_hasDerivAt (coefficient : ℝ) {positive negative : ℝ → ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0)
    (squaresNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ‖negative time‖ < ‖positive time‖)
    (positiveDerivative : HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time)) time)
    (negativeDerivative : HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time)) time) :
    HasDerivAt (fun t => ‖positive t‖ ^ 2 - ‖negative t‖ ^ 2) 0 time := by
  have positiveNorm : 0 < ‖positive time‖ := norm_pos_iff.mpr positiveNonzero
  have ratioPositive : 0 < ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr negativeNonzero)) (sq_pos_of_pos positiveNorm)
  have ratioBelow : ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos positiveNorm)).mpr
    nlinarith [norm_nonneg (negative time)]
  have logarithmic := point_logarithmic_velocities_in_shape coefficient positiveNonzero negativeNonzero
    squaresNonzero ratioPositive ratioBelow rfl (point_shape_phase_identity (positive time) (negative time))
  have balance := shape_logarithmic_radial_balance
    (phase := Complex.arg ((negative time / positive time) ^ 2))
    (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2)) ratioPositive ratioBelow
  convert positiveDerivative.norm_sq.sub negativeDerivative.norm_sq using 1
  rw [real_inner_logarithmic_velocity positiveNonzero,
    real_inner_logarithmic_velocity negativeNonzero, logarithmic.1, logarithmic.2, balance]
  field_simp

def localComplexPhase (reference : ℂ) (field : ℝ → ℂ) (time : ℝ) : ℝ :=
  Complex.arg reference + (Complex.log (field time / reference)).im

theorem localComplexPhase_hasDerivAt {field : ℝ → ℂ} {velocity : ℂ} {time : ℝ}
    (derivative : HasDerivAt field velocity time) (nonzero : field time ≠ 0) :
    HasDerivAt (localComplexPhase (field time) field) (velocity / field time).im time := by
  have slit : field time / field time ∈ Complex.slitPlane := by
    simpa only [div_self nonzero] using Complex.one_mem_slitPlane
  have logarithm := (derivative.div_const (field time)).clog_real slit
  have imaginary := Complex.imCLM.hasFDerivAt.comp_hasDerivAt time logarithm
  simpa only [localComplexPhase, div_self nonzero, div_one, Complex.imCLM_apply,
    zero_add] using imaginary.const_add (Complex.arg (field time))

theorem localComplexPhase_at_reference {field : ℝ → ℂ} {time : ℝ}
    (nonzero : field time ≠ 0) :
    localComplexPhase (field time) field time = Complex.arg (field time) := by
  simp [localComplexPhase, div_self nonzero]

theorem squared_ratio_hasDerivAt {positive negative : ℝ → ℂ} {positiveVelocity negativeVelocity : ℂ}
    {time : ℝ} (positiveDerivative : HasDerivAt positive positiveVelocity time)
    (negativeDerivative : HasDerivAt negative negativeVelocity time)
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0) :
    HasDerivAt (fun t => (negative t / positive t) ^ 2)
      (2 * (negative time / positive time) ^ 2 *
        (negativeVelocity / negative time - positiveVelocity / positive time)) time := by
  have quotient := negativeDerivative.div positiveDerivative positiveNonzero
  convert quotient.mul quotient using 1
  · funext current
    exact pow_two _
  · field_simp
    ring

theorem squared_ratio_phase_hasDerivAt {positive negative : ℝ → ℂ}
    {positiveVelocity negativeVelocity : ℂ} {time : ℝ}
    (positiveDerivative : HasDerivAt positive positiveVelocity time)
    (negativeDerivative : HasDerivAt negative negativeVelocity time)
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0) :
    HasDerivAt
      (localComplexPhase ((negative time / positive time) ^ 2)
        (fun t => (negative t / positive t) ^ 2))
      (2 * (negativeVelocity / negative time - positiveVelocity / positive time).im) time := by
  have ratioNonzero := pow_ne_zero 2 (div_ne_zero negativeNonzero positiveNonzero)
  have derivative := localComplexPhase_hasDerivAt
    (squared_ratio_hasDerivAt positiveDerivative negativeDerivative positiveNonzero negativeNonzero)
    ratioNonzero
  convert derivative using 1
  rw [mul_right_comm (2 : ℂ) ((negative time / positive time) ^ 2),
    mul_div_cancel_right₀ _ ratioNonzero]
  simp

theorem four_point_shape_derivatives (coefficient : ℝ) {positive negative : ℝ → ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0)
    (squaresNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ‖negative time‖ < ‖positive time‖)
    (positiveDerivative : HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time)) time)
    (negativeDerivative : HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time)) time) :
    let ratio := ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2
    let phase := Complex.arg ((negative time / positive time) ^ 2)
    let frequency := coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2)
    HasDerivAt (fun t => ‖negative t‖ ^ 2 / ‖positive t‖ ^ 2)
      (radialVelocity frequency ratio phase) time ∧
    HasDerivAt (localComplexPhase ((negative time / positive time) ^ 2)
      (fun t => (negative t / positive t) ^ 2)) (shapeAngleVelocity frequency ratio phase) time ∧
    HasDerivAt (localComplexPhase (positive time) positive)
      (rotationVelocity frequency ratio phase) time := by
  dsimp only
  have positiveNorm : 0 < ‖positive time‖ := norm_pos_iff.mpr positiveNonzero
  have ratioPositive : 0 < ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr negativeNonzero)) (sq_pos_of_pos positiveNorm)
  have ratioBelow : ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos positiveNorm)).mpr
    nlinarith [norm_nonneg (negative time)]
  have logarithmic := point_logarithmic_velocities_in_shape coefficient positiveNonzero negativeNonzero
    squaresNonzero ratioPositive ratioBelow rfl (point_shape_phase_identity (positive time) (negative time))
  have components := shape_logarithmic_velocity_components
    (phase := Complex.arg ((negative time / positive time) ^ 2))
    (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2)) ratioPositive ratioBelow
  constructor
  · have derivative := norm_ratio_hasDerivAt positiveDerivative negativeDerivative positiveNonzero negativeNonzero
    rw [logarithmic.1, logarithmic.2, components.1] at derivative
    exact derivative
  · constructor
    · have derivative := squared_ratio_phase_hasDerivAt positiveDerivative negativeDerivative positiveNonzero negativeNonzero
      rw [logarithmic.1, logarithmic.2, components.2.1] at derivative
      exact derivative
    · have derivative := localComplexPhase_hasDerivAt positiveDerivative positiveNonzero
      rw [logarithmic.1, components.2.2] at derivative
      exact derivative

theorem four_point_forced_shape_derivatives (coefficient : ℝ) {positive negative : ℝ → ℂ}
    {positiveForcing negativeForcing : ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0)
    (squaresNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ‖negative time‖ < ‖positive time‖)
    (positiveDerivative : HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time) + positiveForcing) time)
    (negativeDerivative : HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time) + negativeForcing) time) :
    let ratio := ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2
    let phase := Complex.arg ((negative time / positive time) ^ 2)
    let frequency := coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2)
    let externalDifference := negativeForcing / negative time - positiveForcing / positive time
    HasDerivAt (fun t => ‖negative t‖ ^ 2 / ‖positive t‖ ^ 2)
      (radialVelocity frequency ratio phase + 2 * ratio * externalDifference.re) time ∧
    HasDerivAt (localComplexPhase ((negative time / positive time) ^ 2)
      (fun t => (negative t / positive t) ^ 2))
      (shapeAngleVelocity frequency ratio phase + 2 * externalDifference.im) time ∧
    HasDerivAt (localComplexPhase (positive time) positive)
      (rotationVelocity frequency ratio phase + (positiveForcing / positive time).im) time := by
  dsimp only
  have positiveNorm : 0 < ‖positive time‖ := norm_pos_iff.mpr positiveNonzero
  have ratioPositive : 0 < ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr negativeNonzero)) (sq_pos_of_pos positiveNorm)
  have ratioBelow : ‖negative time‖ ^ 2 / ‖positive time‖ ^ 2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos positiveNorm)).mpr
    nlinarith [norm_nonneg (negative time)]
  have logarithmic := point_logarithmic_velocities_in_shape coefficient positiveNonzero negativeNonzero
    squaresNonzero ratioPositive ratioBelow rfl (point_shape_phase_identity (positive time) (negative time))
  have components := shape_logarithmic_velocity_components
    (phase := Complex.arg ((negative time / positive time) ^ 2))
    (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2)) ratioPositive ratioBelow
  have differenceIdentity :
      (negativePointVelocity coefficient (positive time) (negative time) + negativeForcing) / negative time -
      (positivePointVelocity coefficient (positive time) (negative time) + positiveForcing) / positive time =
      (negativeShapeLogVelocity (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
        (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2) ((negative time / positive time) ^ 2).arg -
       positiveShapeLogVelocity (coefficient / (‖positive time‖ ^ 2 - ‖negative time‖ ^ 2))
        (‖negative time‖ ^ 2 / ‖positive time‖ ^ 2) ((negative time / positive time) ^ 2).arg) +
      (negativeForcing / negative time - positiveForcing / positive time) := by
    rw [add_div, add_div, logarithmic.1, logarithmic.2]
    ring
  constructor
  · have derivative := norm_ratio_hasDerivAt positiveDerivative negativeDerivative positiveNonzero negativeNonzero
    rw [differenceIdentity, Complex.add_re, mul_add, components.1] at derivative
    exact derivative
  · constructor
    · have derivative := squared_ratio_phase_hasDerivAt positiveDerivative negativeDerivative positiveNonzero negativeNonzero
      rw [differenceIdentity, Complex.add_im, mul_add, components.2.1] at derivative
      exact derivative
    · have derivative := localComplexPhase_hasDerivAt positiveDerivative positiveNonzero
      rw [add_div, logarithmic.1, Complex.add_im, components.2.2] at derivative
      exact derivative

def unwrappedShapeArgument (point : ℂ) : ℝ :=
  if Complex.arg point < 0 then Complex.arg point + 2 * Real.pi else Complex.arg point

def localShapePhase (reference : ℂ) (field : ℝ → ℂ) (time : ℝ) : ℝ :=
  unwrappedShapeArgument reference + (Complex.log (field time / reference)).im

theorem localShapePhase_hasDerivAt {field : ℝ → ℂ} {velocity : ℂ} {time : ℝ}
    (derivative : HasDerivAt field velocity time) (nonzero : field time ≠ 0) :
    HasDerivAt (localShapePhase (field time) field) (velocity / field time).im time := by
  have translated := (localComplexPhase_hasDerivAt derivative nonzero).const_add
    (unwrappedShapeArgument (field time) - Complex.arg (field time))
  convert translated using 1
  funext current
  unfold localShapePhase localComplexPhase
  ring

theorem localShapePhase_at_reference {field : ℝ → ℂ} {time : ℝ}
    (nonzero : field time ≠ 0) :
    localShapePhase (field time) field time = unwrappedShapeArgument (field time) := by
  simp [localShapePhase, div_self nonzero]

theorem point_unwrapped_shape_phase_identity (positive negative : ℂ) :
    (star negative / star positive) ^ 2 =
      shapeConjugateRatio (‖negative‖ ^ 2 / ‖positive‖ ^ 2)
        (unwrappedShapeArgument ((negative / positive) ^ 2)) := by
  rw [point_shape_phase_identity positive negative]
  unfold unwrappedShapeArgument
  split_ifs
  · simp [shapeConjugateRatio, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · rfl

theorem shape_velocities_unwrapped_argument (frequency ratio : ℝ) (point : ℂ) :
    radialVelocity frequency ratio (unwrappedShapeArgument point) =
      radialVelocity frequency ratio (Complex.arg point) ∧
    shapeAngleVelocity frequency ratio (unwrappedShapeArgument point) =
      shapeAngleVelocity frequency ratio (Complex.arg point) ∧
    rotationVelocity frequency ratio (unwrappedShapeArgument point) =
      rotationVelocity frequency ratio (Complex.arg point) := by
  unfold unwrappedShapeArgument
  split_ifs
  · simp [radialVelocity, shapeAngleVelocity, rotationVelocity,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
  · exact ⟨rfl, rfl, rfl⟩

end EulerNonuniqueness.Section6
