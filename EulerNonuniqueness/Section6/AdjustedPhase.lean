import EulerNonuniqueness.Section6.NormalFormChart

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

attribute [local fun_prop] ContDiffAt.sin ContDiffAt.cos

theorem rotationVelocity_phase_derivative (frequency : ℝ) :
    HasDerivAt (fun phase => rotationVelocity frequency rhombusRatio phase) 0 Real.pi := by
  have cosineDerivative : HasDerivAt Real.cos 0 Real.pi := by simpa using Real.hasDerivAt_cos Real.pi
  have numerator := (hasDerivAt_const Real.pi (3 : ℝ)).sub
    (cosineDerivative.const_mul (2 * rhombusRatio)) |>.sub_const (rhombusRatio ^ 2)
  have denominator := ((hasDerivAt_const Real.pi (1 + rhombusRatio ^ 2)).sub
    (cosineDerivative.const_mul (2 * rhombusRatio))).const_mul 2
  have denominatorNonzero : 2 * (1 + rhombusRatio ^ 2 - 2 * rhombusRatio * Real.cos Real.pi) ≠ 0 := by
    rw [Real.cos_pi]
    have ratioPositive := rhombusRatio_pos
    nlinarith [sq_nonneg rhombusRatio]
  simpa [rotationVelocity] using (numerator.const_mul (-frequency * (1 - rhombusRatio))).div
    denominator denominatorNonzero

theorem rotationVelocity_at_pi {frequency ratio : ℝ} (denominatorNonzero : 1 + ratio ≠ 0) :
    rotationVelocity frequency ratio Real.pi = -frequency * (1 - ratio) * (3 - ratio) / (2 * (1 + ratio)) := by
  have squaredDenominator : 1 + ratio ^ 2 + 2 * ratio ≠ 0 := by
    rw [show 1 + ratio ^ 2 + 2 * ratio = (1 + ratio) ^ 2 by ring]
    exact pow_ne_zero 2 denominatorNonzero
  unfold rotationVelocity
  rw [Real.cos_pi]
  field_simp
  ring

theorem rotationVelocity_ratio_derivative (frequency : ℝ) :
    HasDerivAt (fun ratio => rotationVelocity frequency ratio Real.pi)
      (frequency * (Real.sqrt 2 - 1) / rhombusRatio) rhombusRatio := by
  have ratioPositive := rhombusRatio_pos
  have onePlusNonzero : 1 + rhombusRatio ≠ 0 := by positivity
  have numerator := (((hasDerivAt_const rhombusRatio (1 : ℝ)).sub (hasDerivAt_id rhombusRatio)).mul
    ((hasDerivAt_const rhombusRatio (3 : ℝ)).sub (hasDerivAt_id rhombusRatio))).const_mul (-frequency)
  have denominator := ((hasDerivAt_const rhombusRatio (1 : ℝ)).add
    (hasDerivAt_id rhombusRatio)).const_mul 2
  have simplified := numerator.div denominator (mul_ne_zero (by norm_num) onePlusNonzero)
  have constantIdentity : 4 * rhombusRatio * (1 - rhombusRatio) =
      (Real.sqrt 2 - 1) * (1 + rhombusRatio) ^ 2 := by
    unfold rhombusRatio
    have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have cube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        _ = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = _ := by rw [square]
    ring_nf
    rw [cube, square]
    ring
  have derivative : HasDerivAt
      (fun ratio : ℝ => -frequency * (1 - ratio) * (3 - ratio) / (2 * (1 + ratio)))
      (frequency * (Real.sqrt 2 - 1) / rhombusRatio) rhombusRatio := by
    convert simplified using 1
    · funext ratio
      simp only [id_eq]
      ring
    · simp only [id_eq, mul_one, zero_sub, zero_add]
      field_simp
      linear_combination -4 * frequency * constantIdentity +
        2 * frequency * rhombusRatio * rhombusRatio_quadratic
  apply derivative.congr_of_eventuallyEq
  filter_upwards [continuousAt_const.add continuousAt_id |>.eventually_ne onePlusNonzero] with ratio separated
  exact rotationVelocity_at_pi separated

def rawAdjustedPhaseError (frequency : ℝ) (point : ℝ × ℝ) : ℝ :=
  rotationVelocity frequency point.1 point.2 - (Real.sqrt 2 - 1) / 4 *
    shapeAngleVelocity frequency point.1 point.2 + frequency

def adjustedPhaseError (frequency : ℝ) (point : ℝ × ℝ) : ℝ :=
  rawAdjustedPhaseError frequency (shapeChartRatio point, shapeChartAngle point)

theorem rawAdjustedPhaseError_regular (frequency : ℝ) :
    ContDiffAt ℝ 2 (rawAdjustedPhaseError frequency) (rhombusRatio, Real.pi) ∧
      rawAdjustedPhaseError frequency (rhombusRatio, Real.pi) = 0 ∧
      HasFDerivAt (rawAdjustedPhaseError frequency) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (rhombusRatio, Real.pi) := by
  have ratioPositive := rhombusRatio_pos
  have ratioNonzero : rhombusRatio ≠ 0 := ratioPositive.ne'
  have denominatorNonzero : 1 + rhombusRatio ^ 2 + 2 * rhombusRatio ≠ 0 := by positivity
  have smooth : ContDiffAt ℝ 2 (rawAdjustedPhaseError frequency) (rhombusRatio, Real.pi) := by
    unfold rawAdjustedPhaseError rotationVelocity shapeAngleVelocity
    fun_prop (disch := simp_all <;> positivity)
  have firstPartial : HasDerivAt (fun ratio => rawAdjustedPhaseError frequency (ratio, Real.pi)) 0 rhombusRatio := by
    convert ((rotationVelocity_ratio_derivative frequency).sub
      ((shapeAngleVelocity_ratio_derivative frequency).const_mul ((Real.sqrt 2 - 1) / 4))).add_const frequency using 1
    field_simp
    ring
  have secondPartial : HasDerivAt (fun phase => rawAdjustedPhaseError frequency (rhombusRatio, phase)) 0 Real.pi := by
    simpa only [mul_zero, sub_zero] using ((rotationVelocity_phase_derivative frequency).sub
      ((shapeAngleVelocity_phase_derivative frequency).const_mul ((Real.sqrt 2 - 1) / 4))).add_const frequency
  have derivativeZero : fderiv ℝ (rawAdjustedPhaseError frequency) (rhombusRatio, Real.pi) = 0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨horizontal, vertical⟩
    rw [fderiv_apply_of_partial_derivatives (smooth.differentiableAt (by norm_num)) firstPartial secondPartial]
    simp
  refine ⟨smooth, ?_, ?_⟩
  · simp [rawAdjustedPhaseError, rotationVelocity_at_rhombus, shapeAngleVelocity_at_rhombus]
  · rw [← derivativeZero]
    exact (smooth.differentiableAt (by norm_num)).hasFDerivAt

theorem adjustedPhaseError_regular (frequency : ℝ) :
    ContDiffAt ℝ 2 (adjustedPhaseError frequency) 0 ∧ adjustedPhaseError frequency 0 = 0 ∧
      HasFDerivAt (adjustedPhaseError frequency) (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 := by
  have rawRegular := rawAdjustedPhaseError_regular frequency
  have chartSmooth : ContDiffAt ℝ 2 (fun point : ℝ × ℝ => (shapeChartRatio point, shapeChartAngle point)) 0 := by
    unfold shapeChartRatio shapeChartAngle
    fun_prop
  have chartZero : (shapeChartRatio 0, shapeChartAngle 0) = (rhombusRatio, Real.pi) := by
    simp [shapeChartRatio, shapeChartAngle]
  have rawSmooth : ContDiffAt ℝ 2 (rawAdjustedPhaseError frequency) (shapeChartRatio 0, shapeChartAngle 0) := by
    rw [chartZero]
    exact rawRegular.1
  have rawDerivative : HasFDerivAt (rawAdjustedPhaseError frequency) (0 : (ℝ × ℝ) →L[ℝ] ℝ)
      (shapeChartRatio 0, shapeChartAngle 0) := by
    rw [chartZero]
    exact rawRegular.2.2
  refine ⟨ContDiffAt.comp (f := fun point => (shapeChartRatio point, shapeChartAngle point))
    (g := rawAdjustedPhaseError frequency) 0 rawSmooth chartSmooth, ?_, ?_⟩
  · simpa only [adjustedPhaseError, chartZero] using rawRegular.2.1
  · simpa only [ContinuousLinearMap.zero_comp] using rawDerivative.comp (0 : ℝ × ℝ)
      (chartSmooth.differentiableAt (by norm_num)).hasFDerivAt

theorem adjustedPhaseError_quadratic_remainder (frequency : ℝ) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
      |unstable| + |stable| < radius →
        |adjustedPhaseError frequency (unstable, stable)| ≤ bound * (|unstable| + |stable|) ^ 2 := by
  have regular := adjustedPhaseError_regular frequency
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ := contDiffAt_quadratic_remainder regular.1
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro unstable stable sizeBound
  have normBound : ‖(unstable, stable)‖ ≤ |unstable| + |stable| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have result := estimate (unstable, stable) (normBound.trans_lt sizeBound)
  rw [regular.2.1, regular.2.2.fderiv, ContinuousLinearMap.zero_apply, sub_zero, sub_zero,
    Real.norm_eq_abs] at result
  exact result.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) normBound 2) boundNonnegative)

end EulerNonuniqueness.Section6
