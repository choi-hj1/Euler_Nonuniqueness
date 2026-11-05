import EulerNonuniqueness.General.ComplexPairExtensionBounds
import EulerNonuniqueness.Section3.MovingStrainSpectralCorrection
import EulerNonuniqueness.Section3.ContourVelocityLocalSecondRegularity

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance movingStrainGeneratorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentDiskRotatingDerivativeAt_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear independentDiskRotatingDerivativeAt standardCircleBanach := by
  obtain ⟨constant, domain, nearby, regular⟩ :=
    contourVelocity_derivative_hasLipschitzDerivativeNear.lipschitzNear
  let rotation := c1ProductCLM (c1Constant (Complex.I / 2))
  let extension := EulerNonuniqueness.General.complexPairExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
  have extensionRegular := EulerNonuniqueness.General.complexPairExtension_lipschitz
    c1ConjugateCLM c1ConjugateCLM_complex_smul
  let extensionConstant := ‖EulerNonuniqueness.General.complexPairEmbedding c1ConjugateCLM‖₊ *
    (‖EulerNonuniqueness.General.complexPairReal c1ConjugateCLM‖₊ +
      ‖EulerNonuniqueness.General.complexPairImaginary c1ConjugateCLM‖₊)
  have actual : EulerNonuniqueness.General.LipschitzNear
      (fun current => extension (fderiv ℝ extendedContourVelocity current - rotation)) standardCircleBanach := by
    refine ⟨extensionConstant * constant, domain, nearby, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro first firstMember second secondMember
    calc
      _ ≤ (extensionConstant : ℝ) * dist (fderiv ℝ extendedContourVelocity first - rotation)
          (fderiv ℝ extendedContourVelocity second - rotation) := extensionRegular.dist_le_mul _ _
      _ = (extensionConstant : ℝ) * dist (fderiv ℝ extendedContourVelocity first)
          (fderiv ℝ extendedContourVelocity second) := by rw [dist_sub_right]
      _ ≤ (extensionConstant : ℝ) * ((constant : ℝ) * dist first second) :=
        mul_le_mul_of_nonneg_left (regular.dist_le_mul first firstMember second secondMember) (by positivity)
      _ = _ := by dsimp only [extensionConstant]; push_cast; ring
  apply actual.congr
  have thresholdPositive : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have neighborhood : ∀ᶠ current in 𝓝 standardCircleBanach,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have near : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
      simpa only [sub_self, norm_zero] using thresholdPositive
    exact (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds near
  filter_upwards [neighborhood] with current currentSmall
  have rotationJet : HasFDerivAt (c1Product (c1Constant (Complex.I / 2))) rotation current :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) rotation
  have fieldJet := (differentiableAt_extendedContourVelocity current currentSmall).hasFDerivAt.sub rotationJet
  have identity : fderiv ℝ diskEulerRotatingField current = fderiv ℝ extendedContourVelocity current - rotation :=
    fieldJet.fderiv
  change extension (fderiv ℝ diskEulerRotatingField current) = extension (fderiv ℝ extendedContourVelocity current - rotation)
  rw [identity]

end EulerNonuniqueness.Paper
