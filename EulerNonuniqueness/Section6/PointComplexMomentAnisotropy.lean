import EulerNonuniqueness.Section6.PointPhaseVelocity
import EulerNonuniqueness.Section6.DipoleQuadraticMoment

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2 Set

attribute [local fun_prop] ContDiffAt.sin ContDiffAt.cos

def shapeComplexMomentAnisotropy (point : ℝ × ℝ) : ℂ :=
  (1 - shapeConjugateRatio (shapeChartRatio point) (shapeChartAngle point)) /
    ((1 - shapeChartRatio point : ℝ) : ℂ)

theorem fourPointCenteredComplexMoment_eq_odd_difference (positions : FourPointConfiguration) :
    fourPointCenteredComplexMoment positions = 2 * ((fourPointOddPart positions).1 ^ 2 - (fourPointOddPart positions).2 ^ 2) := by
  simp only [fourPointCenteredComplexMoment, fourPointArithmeticCenter, fourPointOddPart, fourPointSign, Fin.sum_univ_succ]
  norm_num
  ring
  rfl

theorem shapeComplexMomentAnisotropy_zero : shapeComplexMomentAnisotropy 0 = (Real.sqrt 2 : ℂ) := by
  have ratioBelow := rhombusRatio_lt_one
  have realIdentity : 1 + rhombusRatio = Real.sqrt 2 * (1 - rhombusRatio) := by
    unfold rhombusRatio
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have shapeValue : shapeConjugateRatio rhombusRatio Real.pi = -(rhombusRatio : ℂ) := by
    apply Complex.ext <;> simp [shapeConjugateRatio]
  simp only [shapeComplexMomentAnisotropy, shapeChartRatio, shapeChartAngle, Prod.fst_zero, Prod.snd_zero,
    add_zero, sub_zero, mul_zero, mul_one, shapeValue, sub_neg_eq_add]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (sub_pos.mpr ratioBelow).ne')).mpr
  exact_mod_cast realIdentity

theorem exists_uniform_complex_moment_anisotropy_bound :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ point : ℝ × ℝ, ‖point‖ < radius →
      ‖shapeComplexMomentAnisotropy point - (Real.sqrt 2 : ℂ)‖ ≤ bound * ‖point‖ := by
  have denominatorNonzero : ((1 - shapeChartRatio (0 : ℝ × ℝ) : ℝ) : ℂ) ≠ 0 := by
    simp only [shapeChartRatio, Prod.fst_zero, Prod.snd_zero, add_zero, mul_one]
    exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr rhombusRatio_lt_one).ne'
  have smooth : ContDiffAt ℝ 1 shapeComplexMomentAnisotropy 0 := by
    have numeratorSmooth : ContDiffAt ℝ 1 (fun point : ℝ × ℝ =>
        1 - shapeConjugateRatio (shapeChartRatio point) (shapeChartAngle point)) 0 := by
      have representation (point : ℝ × ℝ) : shapeConjugateRatio (shapeChartRatio point) (shapeChartAngle point) =
          ((shapeChartRatio point * Real.cos (shapeChartAngle point) : ℝ) : ℂ) -
            ((shapeChartRatio point * Real.sin (shapeChartAngle point) : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp only [shapeConjugateRatio, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
          sub_zero, zero_sub, neg_mul, add_zero]
      simp_rw [representation]
      have realSmooth : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => shapeChartRatio point * Real.cos (shapeChartAngle point)) 0 := by
        unfold shapeChartRatio shapeChartAngle
        fun_prop
      have imaginarySmooth : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => shapeChartRatio point * Real.sin (shapeChartAngle point)) 0 := by
        unfold shapeChartRatio shapeChartAngle
        fun_prop
      exact contDiffAt_const.sub ((Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realSmooth).sub
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp 0 imaginarySmooth).mul contDiffAt_const))
    have denominatorSmooth : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => ((1 - shapeChartRatio point : ℝ) : ℂ)) 0 := by
      have scalarSmooth : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => (1 : ℝ) - shapeChartRatio point) 0 :=
        contDiffAt_const.sub (by unfold shapeChartRatio; fun_prop)
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 scalarSmooth
    simpa only [shapeComplexMomentAnisotropy, div_eq_mul_inv] using numeratorSmooth.mul (denominatorSmooth.inv denominatorNonzero)
  obtain ⟨bound, neighborhood, neighborhoodMember, estimate⟩ := smooth.exists_lipschitzOnWith
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp neighborhoodMember
  refine ⟨bound, bound.coe_nonneg, radius, radiusPositive, ?_⟩
  intro point small
  have inside : point ∈ neighborhood := ballInside (by simpa only [Metric.mem_ball, dist_zero_right] using small)
  have control := estimate.norm_sub_le inside (mem_of_mem_nhds neighborhoodMember)
  simpa only [shapeComplexMomentAnisotropy_zero, sub_zero] using control

theorem point_conjugate_complex_moment_factor {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (normOrder : ‖negative‖ < ‖positive‖) :
    star (positive ^ 2 - negative ^ 2) =
      ((‖positive‖ ^ 2 - ‖negative‖ ^ 2 : ℝ) : ℂ) *
        (star positive ^ 2 / ((‖positive‖ ^ 2 : ℝ) : ℂ)) *
          shapeComplexMomentAnisotropy (pointShapeChart positive negative) := by
  have normSquarePositive : 0 < ‖positive‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr positiveNonzero)
  have ratioBelow : pointShapeRatio positive negative < 1 := by
    apply (div_lt_one normSquarePositive).mpr
    nlinarith [norm_nonneg negative]
  have denominatorNonzero : ((1 - pointShapeRatio positive negative : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_pos.mpr ratioBelow).ne'
  have phase := point_unwrapped_shape_phase_identity positive negative
  change (star negative / star positive) ^ 2 = shapeConjugateRatio (pointShapeRatio positive negative) (pointShapeAngle positive negative) at phase
  rw [shapeComplexMomentAnisotropy, pointShapeChart, (shapeChart_reconstruction _ _).1, (shapeChart_reconstruction _ _).2, ← phase]
  simp only [star_sub, star_pow]
  dsimp only [pointShapeRatio]
  push_cast
  have normNonzero : (‖positive‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr positiveNonzero).ne'
  have gapNonzero : (‖positive‖ : ℂ) ^ 2 - (‖negative‖ : ℂ) ^ 2 ≠ 0 := by
    have realGap : ‖positive‖ ^ 2 - ‖negative‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg negative]
    exact_mod_cast realGap
  rw [one_sub_div (pow_ne_zero 2 normNonzero)]
  have positiveStarNonzero : (starRingEnd ℂ) positive ≠ 0 := star_ne_zero.mpr positiveNonzero
  field_simp [positiveStarNonzero, star_ne_zero.mpr positiveNonzero, normNonzero, gapNonzero]
  <;> ring

theorem exists_uniform_point_complex_moment_phase_error :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ positive negative : ℂ,
      positive ≠ 0 → ‖negative‖ < ‖positive‖ → ‖pointShapeChart positive negative‖ < radius →
      ‖star (positive ^ 2 - negative ^ 2) - (Real.sqrt 2 : ℂ) *
        ((‖positive‖ ^ 2 - ‖negative‖ ^ 2 : ℝ) : ℂ) *
          (star positive ^ 2 / ((‖positive‖ ^ 2 : ℝ) : ℂ))‖ ≤
        bound * |‖positive‖ ^ 2 - ‖negative‖ ^ 2| * ‖pointShapeChart positive negative‖ := by
  obtain ⟨bound, nonnegative, radius, positiveRadius, estimate⟩ := exists_uniform_complex_moment_anisotropy_bound
  refine ⟨bound, nonnegative, radius, positiveRadius, ?_⟩
  intro positive negative positiveNonzero normOrder small
  have directionNorm : ‖star positive ^ 2 / ((‖positive‖ ^ 2 : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, norm_pow, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_self]
    exact (sq_pos_of_pos (norm_pos_iff.mpr positiveNonzero)).ne'
  rw [point_conjugate_complex_moment_factor positiveNonzero normOrder]
  have factorIdentity (difference direction factor : ℂ) : difference * direction * factor -
      (Real.sqrt 2 : ℂ) * difference * direction = difference * direction * (factor - (Real.sqrt 2 : ℂ)) := by ring
  rw [factorIdentity, norm_mul, norm_mul, directionNorm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (estimate _ small) (abs_nonneg _)).trans_eq (by ring)

end EulerNonuniqueness.Section6
