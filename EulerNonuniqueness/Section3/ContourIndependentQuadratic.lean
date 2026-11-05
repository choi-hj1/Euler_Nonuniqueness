import EulerNonuniqueness.Section3.NormalizedShiftDerivative
import EulerNonuniqueness.Section3.DiskForcingModes
import EulerNonuniqueness.General.ComplexPairBilinearExtension

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentQuadraticC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule

local instance independentQuadraticPairOperatorGroup : NormedAddCommGroup
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (σ₁₂ := RingHom.id ℂ)

local instance independentQuadraticPairOperatorSpace : NormedSpace ℂ
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (σ₁₂ := RingHom.id ℂ)

theorem c1ConjugateCLM_complex_smul (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    c1ConjugateCLM (scalar • data) = star scalar • c1ConjugateCLM data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change star (scalar * data.val.1 label) = star scalar * star (data.val.1 label)
  rw [star_mul, mul_comm]

theorem c1ConjugateCLM_involution (data : PeriodicC1HolderHalf) :
    c1ConjugateCLM (c1ConjugateCLM data) = data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  exact star_star _

def contourIndependentEmbedding : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairEmbedding c1ConjugateCLM

def contourIndependentQuadratic :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairBilinearExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    (contourVelocityQuadraticDerivativeCLM standardCircleBanach)

theorem contourIndependentQuadratic_physical (first second : PeriodicC1HolderHalf) :
    contourIndependentQuadratic (contourIndependentEmbedding first) (contourIndependentEmbedding second) =
      contourIndependentEmbedding (contourVelocityQuadraticDerivativeCLM standardCircleBanach first second) := by
  exact EulerNonuniqueness.General.complexPairBilinearExtension_embedding c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
    (contourVelocityQuadraticDerivativeCLM standardCircleBanach) first second

end

end EulerNonuniqueness.Paper
