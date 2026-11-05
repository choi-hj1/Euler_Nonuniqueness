import EulerNonuniqueness.General.ComplexPairBilinearLipschitz
import EulerNonuniqueness.General.LipschitzNearScalar
import EulerNonuniqueness.Section3.MovingStrainGeneratorRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] movingStrainGeneratorC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

local instance movingStrainPairBilinearGroup : NormedAddCommGroup
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (F := (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (σ₁₂ := RingHom.id ℂ)
local instance movingStrainPairBilinearSpace : NormedSpace ℂ
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (F := (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (σ₁₂ := RingHom.id ℂ)

theorem contourIndependentQuadraticAt_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear contourIndependentQuadraticAt standardCircleBanach := by
  have rawRegular : EulerNonuniqueness.General.LipschitzNear
      (fderiv ℝ (fderiv ℝ extendedContourVelocity)) standardCircleBanach :=
    contourVelocity_derivative_hasLipschitzDerivativeNear.2
  have quadraticRegular : EulerNonuniqueness.General.LipschitzNear contourVelocityQuadraticDerivativeCLM
      standardCircleBanach := by
    unfold contourVelocityQuadraticDerivativeCLM
    with_reducible_and_instances
      exact EulerNonuniqueness.General.LipschitzNear.real_smul rawRegular (1 / 2 : ℝ)
  have outer := EulerNonuniqueness.General.complexPairBilinearExtension_lipschitz
    c1ConjugateCLM c1ConjugateCLM_complex_smul
  have outerRegular : EulerNonuniqueness.General.LipschitzNear
      (EulerNonuniqueness.General.complexPairBilinearExtension c1ConjugateCLM c1ConjugateCLM_complex_smul)
      (contourVelocityQuadraticDerivativeCLM standardCircleBanach) :=
    ⟨_, Set.univ, Filter.univ_mem, outer.lipschitzOnWith⟩
  unfold contourIndependentQuadraticAt
  with_reducible_and_instances
    exact outerRegular.comp quadraticRegular

end EulerNonuniqueness.Paper
