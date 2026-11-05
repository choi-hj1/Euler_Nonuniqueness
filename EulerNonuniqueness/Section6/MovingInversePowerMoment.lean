import EulerNonuniqueness.Section3.MovingComplexSpacetimeMoment
import EulerNonuniqueness.Section6.SmoothConjugateInversePower

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem domain_conjugate_inverse_power_hasDerivAt (path : MovingMaterialPatch) {time distance : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime) (distancePositive : 0 < distance)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label))
    (center centerVelocity : ℝ → ℂ) (centerContinuous : Continuous center)
    (centerVelocityContinuous : Continuous centerVelocity)
    (centerDerivative : ∀ parameter, HasDerivAt center (centerVelocity parameter) parameter)
    (separatedNear : ∀ᶠ parameter in 𝓝 time, ∀ position ∈ path.domain parameter,
      distance ≤ ‖center parameter - position‖) (power : ℕ) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter,
      (star (center parameter - position))⁻¹ ^ (power + 1))
      (-((power + 1 : ℕ) : ℂ) * ∫ position in path.domain time,
        star (centerVelocity time - biotSavart source position) *
          (star (center time - position))⁻¹ ^ (power + 2)) time := by
  let kernel := Section6.smoothConjugateInversePower distance (power + 1)
  have kernelSmooth : ContDiff ℝ ∞ kernel := Section6.smoothConjugateInversePower_contDiff distancePositive _
  let centerLinear := fun parameter => (1 : ℝ →L[ℝ] ℝ).smulRight (centerVelocity parameter)
  have centerLinearContinuous : Continuous centerLinear :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1).continuous.comp centerVelocityContinuous
  let displacement := fun point : ℝ × ℂ => center point.1 - point.2
  let displacementDerivative := fun point : ℝ × ℂ =>
    (centerLinear point.1).comp (ContinuousLinearMap.fst ℝ ℝ ℂ) - ContinuousLinearMap.snd ℝ ℝ ℂ
  have displacementContinuous : Continuous displacement := (centerContinuous.comp continuous_fst).sub continuous_snd
  have displacementDerivativeContinuous : Continuous displacementDerivative :=
    ((centerLinearContinuous.comp continuous_fst).clm_comp continuous_const).sub continuous_const
  have displacementHasFDerivAt (point : ℝ × ℂ) :
      HasFDerivAt displacement (displacementDerivative point) point := by
    exact ((centerDerivative point.1).hasFDerivAt.comp point
      (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt).sub (ContinuousLinearMap.snd ℝ ℝ ℂ).hasFDerivAt
  let function := fun point : ℝ × ℂ => kernel (displacement point)
  let derivative := fun point : ℝ × ℂ =>
    (fderiv ℝ kernel (displacement point)).comp (displacementDerivative point)
  have functionContinuous : Continuous function := kernelSmooth.continuous.comp displacementContinuous
  have derivativeContinuous : Continuous derivative :=
    ((kernelSmooth.continuous_fderiv (by simp)).comp displacementContinuous).clm_comp displacementDerivativeContinuous
  have functionDerivative (point : ℝ × ℂ) : HasFDerivAt function (derivative point) point :=
    ((kernelSmooth.differentiable (by simp) (displacement point)).hasFDerivAt).comp point
      (displacementHasFDerivAt point)
  have actual := path.domain_complex_material_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    function derivative functionContinuous derivativeContinuous functionDerivative
  have integralAgreement : (fun parameter => ∫ position in path.domain parameter,
      (star (center parameter - position))⁻¹ ^ (power + 1)) =ᶠ[𝓝 time]
      (fun parameter => ∫ position in path.domain parameter, function (parameter, position)) := by
    filter_upwards [separatedNear] with parameter separated
    apply setIntegral_congr_fun (path.domain_isOpen parameter).measurableSet
    intro position member
    exact ((Section6.smoothConjugateInversePower_eventuallyEq distancePositive (power + 1)
      (separated position member)).eq_of_nhds).symm
  have result := actual.congr_of_eventuallyEq integralAgreement
  convert result using 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (path.domain_isOpen time).measurableSet
  intro position member
  have separated : distance ≤ ‖center time - position‖ := separatedNear.self_of_nhds position member
  have kernelDerivative := Section6.smoothConjugateInversePower_hasFDerivAt distancePositive power separated
  change -((power + 1 : ℕ) : ℂ) *
    (star (centerVelocity time - biotSavart source position) * (star (center time - position))⁻¹ ^ (power + 2)) =
      (fderiv ℝ kernel (center time - position))
        (((centerLinear time).comp (ContinuousLinearMap.fst ℝ ℝ ℂ) -
          ContinuousLinearMap.snd ℝ ℝ ℂ) (1, biotSavart source position))
  rw [kernelDerivative.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    centerLinear,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, smul_eq_mul]
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
    one_smul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, starRingEnd_apply]
  ring

end EulerNonuniqueness.Paper.MovingMaterialPatch
