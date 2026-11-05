import EulerNonuniqueness.Section3.SimilarityPatchDomain
import EulerNonuniqueness.Section3.AffinePatchGreen
import EulerNonuniqueness.Section3.AffinePatchReynolds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem contourAreaPair_rotation (phase : Circle) (first second : ℂ) :
    contourAreaPair ((phase : ℂ) * first) ((phase : ℂ) * second) = contourAreaPair first second := by
  have unitProduct : star (phase : ℂ) * (phase : ℂ) = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := (phase : ℂ))).symm
  unfold contourAreaPair
  have identity : star ((phase : ℂ) * first) * ((phase : ℂ) * second) =
      (star (phase : ℂ) * (phase : ℂ)) * (star first * second) := by
    rw [star_mul]
    ring
  rw [identity, unitProduct, one_mul]

theorem contourAreaPair_similarity (radius : ℝ) (phase : Circle) (first second : ℂ) :
    contourAreaPair (radius • ((phase : ℂ) * first)) (radius • ((phase : ℂ) * second)) =
      radius ^ 2 * contourAreaPair first second := by
  rw [contourAreaPair_real_scaling, contourAreaPair_rotation]

theorem contourPlaneTrace_comp_comm (first second : ℂ →L[ℝ] ℂ) :
    contourPlaneTrace (first.comp second) = contourPlaneTrace (second.comp first) := by
  simp only [contourPlaneTrace, ContinuousLinearMap.comp_apply]
  rw [realLinear_complex_expansion first (second 1), realLinear_complex_expansion first (second Complex.I),
    realLinear_complex_expansion second (first 1), realLinear_complex_expansion second (first Complex.I)]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  ring

theorem contourPlaneTrace_conjugation (equivalence : ℂ ≃L[ℝ] ℂ) (linear : ℂ →L[ℝ] ℂ) :
    contourPlaneTrace (equivalence.symm.toContinuousLinearMap.comp
      (linear.comp equivalence.toContinuousLinearMap)) = contourPlaneTrace linear := by
  rw [contourPlaneTrace_comp_comm]
  have identity : (linear.comp equivalence.toContinuousLinearMap).comp equivalence.symm.toContinuousLinearMap = linear := by
    ext position
    simp
  rw [identity]

def contourSimilarityLinearEquiv {radius : ℝ} (radiusPositive : 0 < radius) (phase : Circle) : ℂ ≃L[ℝ] ℂ :=
  (rotation phase).toContinuousLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ ℂ radius radiusPositive.ne').toContinuousLinearEquiv

theorem contourSimilarityLinearEquiv_apply {radius : ℝ} (radiusPositive : 0 < radius)
    (phase : Circle) (position : ℂ) :
    contourSimilarityLinearEquiv radiusPositive phase position = radius • ((phase : ℂ) * position) := rfl

theorem integral_similarityPatchDomain_divergence
    (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (field : ℂ → ℂ) (derivative : ℂ → ℂ →L[ℝ] ℂ)
    (fieldContinuous : Continuous field) (derivativeContinuous : Continuous derivative)
    (fieldDerivative : ∀ position, HasFDerivAt field (derivative position) position) :
    (∫ position in similarityPatchDomain center radius phase data small, contourPlaneTrace (derivative position)) =
      ∫ label in (-Real.pi)..Real.pi,
        contourAreaPair (field (center + radius • ((phase : ℂ) * data.val.1 label)))
          (radius • ((phase : ℂ) * data.val.2.val.1 label)) := by
  let equivalence := contourSimilarityLinearEquiv radiusPositive phase
  let affine := fun position : ℂ => center + equivalence position
  let pulled := fun position : ℂ => equivalence.symm (field (affine position))
  let pulledDerivative := fun position : ℂ => equivalence.symm.toContinuousLinearMap.comp
    ((derivative (affine position)).comp equivalence.toContinuousLinearMap)
  have affineContinuous : Continuous affine := continuous_const.add equivalence.continuous
  have affineDerivative (position : ℂ) : HasFDerivAt affine equivalence.toContinuousLinearMap position :=
    equivalence.toContinuousLinearMap.hasFDerivAt.const_add center
  have pulledContinuous : Continuous pulled := equivalence.symm.continuous.comp (fieldContinuous.comp affineContinuous)
  have pulledDerivativeContinuous : Continuous pulledDerivative :=
    continuous_const.clm_comp ((derivativeContinuous.comp affineContinuous).clm_comp continuous_const)
  have pulledDerivativeEquation (position : ℂ) : HasFDerivAt pulled (pulledDerivative position) position :=
    equivalence.symm.toContinuousLinearMap.hasFDerivAt.comp position
      ((fieldDerivative (affine position)).comp position (affineDerivative position))
  have green := integral_nearCircleInterior_divergence data small pulled pulledDerivative
    pulledContinuous pulledDerivativeContinuous pulledDerivativeEquation
  have traceIdentity (position : ℂ) : contourPlaneTrace (pulledDerivative position) =
      contourPlaneTrace (derivative (affine position)) := contourPlaneTrace_conjugation equivalence _
  simp_rw [traceIdentity] at green
  rw [integral_similarityPatchDomain center radiusPositive phase data small]
  change radius ^ 2 * (∫ position in nearCircleInterior data small, contourPlaneTrace (derivative (affine position))) = _
  rw [green, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro label _
  have pairIdentity := contourAreaPair_similarity radius phase
    (equivalence.symm (field (affine (data.val.1 label)))) (data.val.2.val.1 label)
  change contourAreaPair (equivalence (equivalence.symm (field (affine (data.val.1 label)))))
    (equivalence (data.val.2.val.1 label)) = _ at pairIdentity
  rw [equivalence.apply_symm_apply] at pairIdentity
  exact pairIdentity.symm

theorem integral_similarityPatchDomain_directional_field
    (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (scalarDerivative : ℂ → ℂ →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (scalarDerivativeContinuous : Continuous scalarDerivative)
    (functionDerivative : ∀ position, HasFDerivAt function (scalarDerivative position) position)
    (field : ℂ → ℂ) (fieldDerivative : ℂ → ℂ →L[ℝ] ℂ)
    (fieldContinuous : Continuous field) (fieldDerivativeContinuous : Continuous fieldDerivative)
    (fieldDerivativeEquation : ∀ position, HasFDerivAt field (fieldDerivative position) position)
    (divergenceZero : ∀ position, contourPlaneTrace (fieldDerivative position) = 0) :
    (∫ position in similarityPatchDomain center radius phase data small, scalarDerivative position (field position)) =
      ∫ label in (-Real.pi)..Real.pi, function (center + radius • ((phase : ℂ) * data.val.1 label)) *
        contourAreaPair (field (center + radius • ((phase : ℂ) * data.val.1 label)))
          (radius • ((phase : ℂ) * data.val.2.val.1 label)) := by
  let productDerivative : ℂ → ℂ →L[ℝ] ℂ := fun position =>
    (scalarDerivative position).smulRight (field position) + function position • fieldDerivative position
  have productDerivativeContinuous : Continuous productDerivative := by
    apply Continuous.add
    · exact Continuous.clm_apply
        ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp scalarDerivativeContinuous) fieldContinuous
    · exact functionContinuous.smul fieldDerivativeContinuous
  have green := integral_similarityPatchDomain_divergence center radiusPositive phase data small
    (fun position => function position • field position) productDerivative
    (functionContinuous.smul fieldContinuous) productDerivativeContinuous
    (fun position => by
      simpa only [productDerivative, add_comm] using (functionDerivative position).smul (fieldDerivativeEquation position))
  have traceIdentity (position : ℂ) : contourPlaneTrace (productDerivative position) = scalarDerivative position (field position) := by
    dsimp only [productDerivative]
    rw [contourPlaneTrace_smul_product, divergenceZero position, mul_zero, add_zero]
  simp_rw [traceIdentity] at green
  rw [green]
  apply intervalIntegral.integral_congr
  intro label _
  simp only [contourAreaPair_coordinates, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  ring

theorem similarityPatchDomain_integrable_of_continuous
    {value : Type*} [NormedAddCommGroup value] [NormedSpace ℝ value]
    (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    {function : ℂ → value} (functionContinuous : Continuous function) :
    IntegrableOn function (similarityPatchDomain center radius phase data small) :=
  (functionContinuous.continuousOn.integrableOn_compact
    (similarityPatchDomain_isBounded center radiusPositive phase data small).isCompact_closure).mono_set subset_closure

end EulerNonuniqueness.Paper
