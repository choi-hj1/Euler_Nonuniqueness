import EulerNonuniqueness.Section6.RhombusStrain

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

attribute [local fun_prop] ContDiffAt.sin ContDiffAt.cos

def shapeChartStrainField (point strain : ℝ × ℝ) : ℝ × ℝ :=
  let realDifference := strain.1 * (Real.cos (shapeChartAngle point) - 1) +
    strain.2 * Real.sin (shapeChartAngle point)
  let imaginaryDifference := strain.2 * (Real.cos (shapeChartAngle point) - 1) -
    strain.1 * Real.sin (shapeChartAngle point)
  (shapeChartRatio point / rhombusRatio * realDifference + imaginaryDifference / Real.sqrt 2,
    shapeChartRatio point / rhombusRatio * realDifference - imaginaryDifference / Real.sqrt 2)

theorem shapeChartStrainField_zero (strain : ℝ × ℝ) :
    shapeChartStrainField 0 strain =
      (-2 * strain.1 - Real.sqrt 2 * strain.2, -2 * strain.1 + Real.sqrt 2 * strain.2) := by
  have sqrtTwoNonzero := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [shapeChartStrainField, shapeChartAngle, shapeChartRatio, Prod.fst_zero, Prod.snd_zero,
    zero_add, add_zero, mul_zero, one_mul, mul_one, Real.cos_pi, Real.sin_pi, div_self rhombusRatio_pos.ne']
  apply Prod.ext <;> dsimp <;> field_simp [sqrtTwoNonzero] <;>
    ring_nf <;> simp [Real.sq_sqrt] <;> ring

theorem shapeChartStrainField_linear (point strain : ℝ × ℝ) :
    shapeChartStrainField point strain = strain.1 • shapeChartStrainField point (1, 0) +
      strain.2 • shapeChartStrainField point (0, 1) := by
  apply Prod.ext <;> dsimp [shapeChartStrainField] <;> ring

theorem shapeChartStrainField_contDiffAt (strain : ℝ × ℝ) :
    ContDiffAt ℝ 1 (fun point => shapeChartStrainField point strain) 0 := by
  unfold shapeChartStrainField shapeChartRatio shapeChartAngle
  fun_prop (disch := first | exact rhombusRatio_pos.ne' | positivity)

theorem external_strain_logarithmic_difference {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0) (strain : ℂ) :
    strain * star negative / negative - strain * star positive / positive =
      (strain * star positive / positive) *
        ((star negative / star positive) ^ 2 /
          ((pointShapeRatio positive negative : ℝ) : ℂ) - 1) := by
  have positiveProduct : positive * star positive = (‖positive‖ ^ 2 : ℝ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj positive
  have negativeProduct : negative * star negative = (‖negative‖ ^ 2 : ℝ) := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj negative
  have ratioIdentity : ((pointShapeRatio positive negative : ℝ) : ℂ) =
      (negative * star negative) / (positive * star positive) := by
    rw [positiveProduct, negativeProduct]
    simp only [pointShapeRatio, Complex.ofReal_div]
  rw [ratioIdentity]
  have positiveStarNonzero : star positive ≠ 0 := star_ne_zero.mpr positiveNonzero
  have negativeStarNonzero : star negative ≠ 0 := star_ne_zero.mpr negativeNonzero
  field_simp [positiveNonzero, negativeNonzero, positiveStarNonzero, negativeStarNonzero]
  ring

theorem shapeConjugateRatio_div_ratio {ratio : ℝ} (ratioNonzero : ratio ≠ 0) (phase : ℝ) :
    shapeConjugateRatio ratio phase / (ratio : ℂ) = ⟨Real.cos phase, -Real.sin phase⟩ := by
  apply Complex.ext <;> simp [shapeConjugateRatio, Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp <;> ring

theorem pointShapeForcing_eq_shapeChartStrainField {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0) (strain : ℂ) :
    pointShapeForcing positive negative (strain * star positive) (strain * star negative) =
      shapeChartStrainField (pointShapeChart positive negative)
        ((strain * star positive / positive).re, (strain * star positive / positive).im) := by
  have ratioNonzero : pointShapeRatio positive negative ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr negativeNonzero))
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr positiveNonzero))
  have logarithmic := external_strain_logarithmic_difference positiveNonzero negativeNonzero strain
  rw [point_unwrapped_shape_phase_identity] at logarithmic
  simp only [pointShapeRatio] at logarithmic ratioNonzero
  rw [shapeConjugateRatio_div_ratio ratioNonzero] at logarithmic
  unfold shapeChartStrainField pointShapeForcing
  simp only [pointShapeChart]
  rw [(shapeChart_reconstruction (pointShapeRatio positive negative) (pointShapeAngle positive negative)).1,
    (shapeChart_reconstruction (pointShapeRatio positive negative) (pointShapeAngle positive negative)).2]
  rw [logarithmic]
  apply Prod.ext <;> dsimp [pointShapeAngle] <;> ring

theorem shapeChartStrainField_remainder :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ point strain : ℝ × ℝ, ‖point‖ < radius →
      ‖shapeChartStrainField point strain - shapeChartStrainField 0 strain‖ ≤
        bound * ‖strain‖ * ‖point‖ := by
  obtain ⟨firstBound, firstPositive, firstEstimate⟩ :=
    ((shapeChartStrainField_contDiffAt (1, 0)).differentiableAt (by norm_num)).hasFDerivAt.isBigO_sub.exists_pos
  obtain ⟨secondBound, secondPositive, secondEstimate⟩ :=
    ((shapeChartStrainField_contDiffAt (0, 1)).differentiableAt (by norm_num)).hasFDerivAt.isBigO_sub.exists_pos
  have estimates : ∀ᶠ point in nhds (0 : ℝ × ℝ),
      ‖shapeChartStrainField point (1, 0) - shapeChartStrainField 0 (1, 0)‖ ≤ firstBound * ‖point‖ ∧
      ‖shapeChartStrainField point (0, 1) - shapeChartStrainField 0 (0, 1)‖ ≤ secondBound * ‖point‖ := by
    filter_upwards [firstEstimate.bound, secondEstimate.bound] with point first second
    simpa only [sub_zero] using And.intro first second
  obtain ⟨radius, radiusPositive, inside⟩ := Metric.mem_nhds_iff.mp estimates
  refine ⟨firstBound + secondBound, by positivity, radius, radiusPositive, ?_⟩
  intro point strain pointBound
  have estimates := inside (show point ∈ Metric.ball 0 radius by simpa using pointBound)
  have firstCoefficient : |strain.1| ≤ ‖strain‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le strain
  have secondCoefficient : |strain.2| ≤ ‖strain‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le strain
  calc
    ‖shapeChartStrainField point strain - shapeChartStrainField 0 strain‖ =
        ‖strain.1 • (shapeChartStrainField point (1, 0) - shapeChartStrainField 0 (1, 0)) +
          strain.2 • (shapeChartStrainField point (0, 1) - shapeChartStrainField 0 (0, 1))‖ := by
      congr 1
      rw [shapeChartStrainField_linear point strain, shapeChartStrainField_linear 0 strain]
      module
    _ ≤ |strain.1| * ‖shapeChartStrainField point (1, 0) - shapeChartStrainField 0 (1, 0)‖ +
        |strain.2| * ‖shapeChartStrainField point (0, 1) - shapeChartStrainField 0 (0, 1)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (strain.1 • (shapeChartStrainField point (1, 0) - shapeChartStrainField 0 (1, 0)))
        (strain.2 • (shapeChartStrainField point (0, 1) - shapeChartStrainField 0 (0, 1)))
    _ ≤ |strain.1| * (firstBound * ‖point‖) + |strain.2| * (secondBound * ‖point‖) :=
      add_le_add (mul_le_mul_of_nonneg_left estimates.1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left estimates.2 (abs_nonneg _))
    _ ≤ ‖strain‖ * (firstBound * ‖point‖) + ‖strain‖ * (secondBound * ‖point‖) := by
      gcongr
    _ = (firstBound + secondBound) * ‖strain‖ * ‖point‖ := by ring

theorem pointShapeForcing_strain_remainder :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ positive negative strain : ℂ,
      positive ≠ 0 → negative ≠ 0 →
      |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| < radius →
      let logarithmic := strain * star positive / positive
      ‖pointShapeForcing positive negative (strain * star positive) (strain * star negative) -
        (-2 * logarithmic.re - Real.sqrt 2 * logarithmic.im,
          -2 * logarithmic.re + Real.sqrt 2 * logarithmic.im)‖ ≤
        bound * ‖strain‖ * (|(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2|) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ := shapeChartStrainField_remainder
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro positive negative strain positiveNonzero negativeNonzero sizeBound
  dsimp only
  have pointNorm : ‖pointShapeChart positive negative‖ ≤
      |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have logarithmicNorm : ‖strain * star positive / positive‖ = ‖strain‖ := by
    rw [norm_div, norm_mul, norm_star]
    exact mul_div_cancel_right₀ ‖strain‖ (norm_ne_zero_iff.mpr positiveNonzero)
  have strainNorm : ‖((strain * star positive / positive).re, (strain * star positive / positive).im)‖ ≤
      ‖strain‖ := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le ((Complex.abs_re_le_norm _).trans logarithmicNorm.le)
      ((Complex.abs_im_le_norm _).trans logarithmicNorm.le)
  have result := estimate (pointShapeChart positive negative)
    ((strain * star positive / positive).re, (strain * star positive / positive).im)
    (pointNorm.trans_lt sizeBound)
  rw [shapeChartStrainField_zero] at result
  rw [pointShapeForcing_eq_shapeChartStrainField positiveNonzero negativeNonzero]
  exact result.trans (mul_le_mul (mul_le_mul_of_nonneg_left strainNorm boundNonnegative)
    pointNorm (norm_nonneg _) (by positivity))

end EulerNonuniqueness.Section6
