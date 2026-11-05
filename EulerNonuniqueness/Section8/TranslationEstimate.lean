import EulerNonuniqueness.Section8.WeakGradient
import EulerNonuniqueness.General.NormJensen

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integral_translation_sub_sq_le {velocity : Velocity}
    (smooth : ContDiff ℝ ∞ velocity) (velocityMember : MemLp velocity 2 volume)
    (offset : Plane) (gradientMember : MemLp (fun position => fderiv ℝ velocity position offset) 2 volume) :
    (∫ position, ‖velocity (position + offset) - velocity position‖ ^ 2) ≤
      ∫ position, ‖fderiv ℝ velocity position offset‖ ^ 2 := by
  let intervalMeasure : Measure ℝ := volume.restrict (Icc 0 1)
  letI : IsProbabilityMeasure intervalMeasure := ⟨by simp [intervalMeasure]⟩
  have derivativeContinuous : Continuous (fun position => fderiv ℝ velocity position offset) :=
    (smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have pathDerivative (position : Plane) (parameter : ℝ) :
      HasDerivAt (fun time : ℝ => velocity (position + time • offset))
        (fderiv ℝ velocity (position + parameter • offset) offset) parameter := by
    have path : HasDerivAt (fun time : ℝ => position + time • offset) offset parameter := by
      simpa using (hasDerivAt_const parameter position).add ((hasDerivAt_id parameter).smul_const offset)
    exact (smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt parameter path
  have pathContinuous (position : Plane) :
      Continuous (fun parameter : ℝ => fderiv ℝ velocity (position + parameter • offset) offset) :=
    derivativeContinuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have pathIntegral (position : Plane) :
      (∫ parameter, fderiv ℝ velocity (position + parameter • offset) offset ∂intervalMeasure) =
        velocity (position + offset) - velocity position := by
    rw [show intervalMeasure = volume.restrict (Icc (0 : ℝ) 1) from rfl,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun parameter _ => pathDerivative position parameter) ((pathContinuous position).intervalIntegrable 0 1)
  have pointwise (position : Plane) :
      ‖velocity (position + offset) - velocity position‖ ^ 2 ≤
        ∫ parameter, ‖fderiv ℝ velocity (position + parameter • offset) offset‖ ^ 2 ∂intervalMeasure := by
    rw [← pathIntegral]
    exact norm_integral_pow_le_integral_norm_pow
      ((pathContinuous position).continuousOn.integrableOn_compact isCompact_Icc) 2
      (((pathContinuous position).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have jointMeasurable : AEStronglyMeasurable
      (fun point : Plane × ℝ => ‖fderiv ℝ velocity (point.1 + point.2 • offset) offset‖ ^ 2)
      (volume.prod intervalMeasure) :=
    ((derivativeContinuous.comp (continuous_fst.add (continuous_snd.smul continuous_const))).norm.pow 2).aestronglyMeasurable
  have shiftedIntegral (parameter : ℝ) :
      (∫ position, ‖fderiv ℝ velocity (position + parameter • offset) offset‖ ^ 2) =
        ∫ position, ‖fderiv ℝ velocity position offset‖ ^ 2 :=
    integral_add_right_eq_self (fun position => ‖fderiv ℝ velocity position offset‖ ^ 2) (parameter • offset)
  have jointIntegrable : Integrable
      (fun point : Plane × ℝ => ‖fderiv ℝ velocity (point.1 + point.2 • offset) offset‖ ^ 2)
      (volume.prod intervalMeasure) := by
    apply (integrable_prod_iff' jointMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun parameter =>
        (gradientMember.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_add_right (parameter • offset)
    · simp only [Real.norm_eq_abs, abs_pow, abs_norm, shiftedIntegral]
      exact integrable_const _
  have differenceMember : MemLp (fun position => velocity (position + offset) - velocity position) 2 volume :=
    (velocityMember.comp_measurePreserving (measurePreserving_add_right volume offset)).sub velocityMember
  calc
    _ ≤ ∫ position, ∫ parameter,
        ‖fderiv ℝ velocity (position + parameter • offset) offset‖ ^ 2 ∂intervalMeasure :=
      integral_mono (differenceMember.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
        jointIntegrable.integral_prod_left pointwise
    _ = ∫ parameter, (∫ position,
        ‖fderiv ℝ velocity (position + parameter • offset) offset‖ ^ 2) ∂intervalMeasure :=
      integral_integral_swap jointIntegrable
    _ = _ := by simp only [shiftedIntegral, integral_const, measureReal_univ_eq_one, one_smul]

theorem norm_realLinearMap_apply_sq_le (linear : Plane →L[ℝ] Plane) (offset : Plane) :
    ‖linear offset‖ ^ 2 ≤ ‖offset‖ ^ 2 * (‖linear 1‖ ^ 2 + ‖linear Complex.I‖ ^ 2) := by
  have split : offset = offset.re • (1 : ℂ) + offset.im • Complex.I := by
    simp only [Complex.real_smul, mul_one]
    exact offset.re_add_im.symm
  have application : linear offset = offset.re • linear 1 + offset.im • linear Complex.I := by
    calc
      _ = linear (offset.re • (1 : ℂ) + offset.im • Complex.I) := congrArg linear split
      _ = _ := by rw [map_add, map_smul, map_smul]
  have normBound : ‖linear offset‖ ≤ |offset.re| * ‖linear 1‖ + |offset.im| * ‖linear Complex.I‖ := by
    rw [application]
    simpa only [norm_smul, Real.norm_eq_abs] using
      norm_add_le (offset.re • linear 1) (offset.im • linear Complex.I)
  calc
    _ ≤ (|offset.re| * ‖linear 1‖ + |offset.im| * ‖linear Complex.I‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) normBound 2
    _ ≤ _ := by
      rw [Complex.sq_norm offset, Complex.normSq_apply]
      simp only [← pow_two]
      rw [← sq_abs offset.re, ← sq_abs offset.im]
      nlinarith only [sq_nonneg (|offset.re| * ‖linear Complex.I‖ - |offset.im| * ‖linear 1‖)]

theorem eLpNorm_translation_biotSavart_smooth_le {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (zeroMean : (∫ position, vorticity position) = 0) (offset : Plane) :
    (eLpNorm (fun position => biotSavart vorticity (position + offset) - biotSavart vorticity position) 2 volume).toReal ≤
      ‖offset‖ * (eLpNorm vorticity 2 volume).toReal := by
  have velocityMember := memLp_biotSavart_two_of_continuous_compactSupport_integral_zero smooth.continuous compact zeroMean
  have firstMember := memLp_fderiv_biotSavart_apply smooth compact 1
  have secondMember := memLp_fderiv_biotSavart_apply smooth compact Complex.I
  have offsetMember := memLp_fderiv_biotSavart_apply smooth compact offset
  have differenceMember :=
    (velocityMember.comp_measurePreserving (measurePreserving_add_right volume offset)).sub velocityMember
  change MemLp (fun position => biotSavart vorticity (position + offset) - biotSavart vorticity position) 2 volume at differenceMember
  have sourceMember : MemLp vorticity 2 volume := smooth.continuous.memLp_of_hasCompactSupport compact
  have pointwise : ∀ position : Plane, ‖fderiv ℝ (biotSavart vorticity) position offset‖ ^ 2 ≤
      ‖offset‖ ^ 2 * (‖fderiv ℝ (biotSavart vorticity) position 1‖ ^ 2 +
        ‖fderiv ℝ (biotSavart vorticity) position Complex.I‖ ^ 2) :=
    fun position => norm_realLinearMap_apply_sq_le _ offset
  have gradientBound := integral_mono
    (offsetMember.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (((firstMember.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).add
      (secondMember.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).const_mul (‖offset‖ ^ 2)) pointwise
  rw [integral_const_mul] at gradientBound
  simp only [Pi.add_apply] at gradientBound
  rw [integral_gradient_biotSavart_sq smooth compact zeroMean] at gradientBound
  have translatedBound := (integral_translation_sub_sq_le
    (contDiff_biotSavart_of_contDiff_compactSupport smooth compact) velocityMember offset offsetMember).trans gradientBound
  have sourceSquare : (∫ position, vorticity position ^ 2) = (eLpNorm vorticity 2 volume).toReal ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (toReal_eLpNorm_two_sq_eq_integral sourceMember).symm
  rw [← toReal_eLpNorm_two_sq_eq_integral differenceMember, sourceSquare] at translatedBound
  have nonnegative : 0 ≤
      (eLpNorm (fun position => biotSavart vorticity (position + offset) - biotSavart vorticity position) 2 volume).toReal :=
    ENNReal.toReal_nonneg
  have sourceNonnegative : 0 ≤ (eLpNorm vorticity 2 volume).toReal := ENNReal.toReal_nonneg
  nlinarith only [translatedBound, nonnegative, mul_nonneg (norm_nonneg offset) sourceNonnegative]

theorem eLpNorm_translation_biotSavart_le {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0) (offset : Plane) :
    eLpNorm (fun position => biotSavart vorticity (position + offset) - biotSavart vorticity position) 2 volume ≤
      ENNReal.ofReal (‖offset‖ * (eLpNorm vorticity 2 volume).toReal) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sourceMember : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have sourceBound (index : ℕ) : (eLpNorm (mollification vorticity index) 2 volume).toReal ≤
      (eLpNorm vorticity 2 volume).toReal :=
    ENNReal.toReal_mono sourceMember.eLpNorm_ne_top
      (eLpNorm_mollification_nat_le integrable supportBound (by norm_num : 0 < 2) sourceMember index)
  have mollifiedMean (index : ℕ) : (∫ position, mollification vorticity index position) = 0 := by
    rw [integral_mollification integrable index, zeroMean]
  have bound (index : ℕ) :
      eLpNorm (fun position => biotSavart (mollification vorticity index) (position + offset) -
        biotSavart (mollification vorticity index) position) 2 volume ≤
      ENNReal.ofReal (‖offset‖ * (eLpNorm vorticity 2 volume).toReal) := by
    have velocityMember := memLp_biotSavart_two_of_continuous_compactSupport_integral_zero
      (contDiff_mollification integrable index).continuous
      (hasCompactSupport_mollification supportBound index) (mollifiedMean index)
    have differenceMember :=
      (velocityMember.comp_measurePreserving (measurePreserving_add_right volume offset)).sub velocityMember
    change MemLp (fun position => biotSavart (mollification vorticity index) (position + offset) -
      biotSavart (mollification vorticity index) position) 2 volume at differenceMember
    rw [← ENNReal.ofReal_toReal differenceMember.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    exact (eLpNorm_translation_biotSavart_smooth_le (contDiff_mollification integrable index)
      (hasCompactSupport_mollification supportBound index) (mollifiedMean index) offset).trans
      (mul_le_mul_of_nonneg_left (sourceBound index) (norm_nonneg offset))
  have fatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) (μ := volume)
    (fun index =>
      ((continuous_biotSavart_of_continuous_compactSupport (contDiff_mollification integrable index).continuous
        (hasCompactSupport_mollification supportBound index)).comp (continuous_id.add continuous_const)).aestronglyMeasurable.sub
        (continuous_biotSavart_of_continuous_compactSupport (contDiff_mollification integrable index).continuous
          (hasCompactSupport_mollification supportBound index)).aestronglyMeasurable)
    (fun position => biotSavart vorticity (position + offset) - biotSavart vorticity position)
    (Filter.Eventually.of_forall fun position =>
      (tendsto_biotSavart_mollification radiusNonnegative membership supportBound (position + offset)).sub
        (tendsto_biotSavart_mollification radiusNonnegative membership supportBound position))
  simp only [Function.comp_apply, Pi.sub_apply] at fatou
  exact fatou.trans (Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall bound).frequently)

end EulerNonuniqueness
