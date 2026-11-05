import EulerNonuniqueness.Definitions
import EulerNonuniqueness.General.RadialRotationField

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem spatialDerivative_temporal_smul {temporal : ℝ → ℝ} {spatial : Plane → Plane}
    {point : ℝ × Plane} (temporalDifferentiable : DifferentiableAt ℝ temporal point.1)
    (spatialDifferentiable : DifferentiableAt ℝ spatial point.2) (direction : Plane) :
    spatialDerivative (fun other : ℝ × Plane => temporal other.1 • spatial other.2) point direction =
      temporal point.1 • fderiv ℝ spatial point.2 direction := by
  have scalar := temporalDifferentiable.hasFDerivAt.comp point hasFDerivAt_fst
  have field := spatialDifferentiable.hasFDerivAt.comp point hasFDerivAt_snd
  have derivative := scalar.smul field
  simp only [Function.comp_def] at derivative
  rw [spatialDerivative, derivative.fderiv]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    map_zero, zero_smul, zero_add, ContinuousLinearMap.smul_apply]
  change temporal point.1 • fderiv ℝ spatial point.2 direction +
    fderiv ℝ temporal point.1 0 • spatial point.2 = _
  simp only [map_zero, zero_smul, add_zero]

theorem divergence_temporal_radialRotationField {temporal profile : ℝ → ℝ}
    (temporalSmooth : ContDiff ℝ ∞ temporal) (profileSmooth : ContDiff ℝ ∞ profile) (point : ℝ × Plane) :
    spatialDivergence (fun other : ℝ × Plane => temporal other.1 • Complex.radialRotationField profile other.2) point = 0 := by
  have temporalDifferentiable : DifferentiableAt ℝ temporal point.1 :=
    (temporalSmooth.differentiable (by simp)).differentiableAt
  have spatialDifferentiable : DifferentiableAt ℝ (Complex.radialRotationField profile) point.2 :=
    ((Complex.contDiff_radialRotationField profileSmooth).differentiable (by simp)).differentiableAt
  rw [spatialDivergence, spatialDerivative_temporal_smul temporalDifferentiable spatialDifferentiable,
    spatialDerivative_temporal_smul temporalDifferentiable spatialDifferentiable]
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [← mul_add, Complex.divergence_radialRotationField
    ((profileSmooth.differentiable (by simp)).differentiableAt), mul_zero]

theorem exists_nonzero_vectorTestOn (horizon : ℝ) (positive : 0 < horizon) :
    ∃ test : ℝ × Plane → Plane, VectorTestOn horizon test ∧ test (horizon / 2, 1) = Complex.I := by
  let temporal : ContDiffBump (horizon / 2) := ⟨horizon / 8, horizon / 4, by positivity, by linarith⟩
  let profile : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let test : ℝ × Plane → Plane := fun point => temporal point.1 • Complex.radialRotationField profile point.2
  have testSmooth : ContDiff ℝ ∞ test :=
    (temporal.contDiff.comp contDiff_fst).smul
      ((Complex.contDiff_radialRotationField profile.contDiff).comp contDiff_snd)
  have testCompact : HasCompactSupport test := by
    apply HasCompactSupport.intro
      ((isCompact_closedBall (horizon / 2) (horizon / 4)).prod (isCompact_closedBall (0 : Plane) 2))
    intro point outside
    by_cases timeInside : point.1 ∈ Metric.closedBall (horizon / 2) (horizon / 4)
    · have positionOutside : point.2 ∉ Metric.closedBall (0 : Plane) 2 := fun inside => outside ⟨timeInside, inside⟩
      have large : 2 < ‖point.2‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using positionOutside
      have profileZero : profile (‖point.2‖ ^ 2) = 0 := by
        apply profile.zero_of_le_dist
        change 2 ≤ dist (‖point.2‖ ^ 2) (0 : ℝ)
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith
      simp only [test, Complex.radialRotationField, profileZero, zero_smul, smul_zero]
    · have temporalZero : temporal point.1 = 0 := by
        apply temporal.zero_of_le_dist
        exact (lt_of_not_ge (show ¬dist point.1 (horizon / 2) ≤ horizon / 4 from timeInside)).le
      simp only [test, temporalZero, zero_smul]
  refine ⟨test, ⟨testSmooth, testCompact, ?_, divergence_temporal_radialRotationField temporal.contDiff profile.contDiff⟩, ?_⟩
  · intro time position after
    have temporalZero : temporal time = 0 := by
      apply temporal.zero_of_le_dist
      change horizon / 4 ≤ dist time (horizon / 2)
      rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ time - horizon / 2)]
      linarith
    simp only [test, temporalZero, zero_smul]
  · have profileOne : profile (‖(1 : Plane)‖ ^ 2) = 1 := by
      apply profile.one_of_mem_closedBall
      norm_num [Metric.mem_closedBall, Real.dist_eq, profile]
    have temporalOne : temporal (horizon / 2) = 1 :=
      temporal.one_of_mem_closedBall (Metric.mem_closedBall_self temporal.rIn_pos.le)
    simp only [test, temporalOne, Complex.radialRotationField, profileOne,
      one_smul, mul_one]

theorem spatialDerivative_vector_time_translation {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (shift : ℝ) (point : ℝ × Plane) (direction : Plane) :
    spatialDerivative (fun other : ℝ × Plane => test ((shift, 0) + other)) point direction =
      spatialDerivative test (shift + point.1, point.2) direction := by
  have derivative := ((smooth.differentiable (by simp)) ((shift, (0 : Plane)) + point)).hasFDerivAt.comp point
    ((hasFDerivAt_const (shift, (0 : Plane)) point).add (hasFDerivAt_id point))
  change fderiv ℝ (test ∘ HAdd.hAdd (shift, (0 : Plane))) point (0, direction) = _
  rw [derivative.fderiv]
  simp [spatialDerivative, ContinuousLinearMap.comp_apply, Prod.add_def]

theorem exists_vectorTestOn_with_nonzero_initial_trace (horizon : ℝ) (positive : 0 < horizon) :
    ∃ test : ℝ × Plane → Plane, VectorTestOn horizon test ∧ test (0, 1) = Complex.I := by
  obtain ⟨test, admissible, atCenter⟩ := exists_nonzero_vectorTestOn (2 * horizon) (by positivity)
  let shifted : ℝ × Plane → Plane := fun point => test ((horizon, 0) + point)
  have smooth : ContDiff ℝ ∞ shifted := admissible.1.comp (contDiff_const.add contDiff_id)
  have compact : HasCompactSupport shifted := by
    simpa only [shifted, Function.comp_def, Homeomorph.addLeft] using
      admissible.2.1.comp_homeomorph (Homeomorph.addLeft (horizon, (0 : Plane)))
  refine ⟨shifted, ⟨smooth, compact, ?_, ?_⟩, ?_⟩
  · intro time position after
    simpa only [shifted, Prod.add_def, zero_add] using
      admissible.2.2.1 (horizon + time) position (by linarith)
  · intro point
    change (spatialDerivative shifted point 1).re + (spatialDerivative shifted point Complex.I).im = 0
    rw [spatialDerivative_vector_time_translation admissible.1, spatialDerivative_vector_time_translation admissible.1]
    exact admissible.2.2.2 (horizon + point.1, point.2)
  · have centered : 2 * horizon / 2 = horizon := by ring
    simpa only [shifted, Prod.add_def, add_zero, zero_add, centered] using atCenter

end EulerNonuniqueness
