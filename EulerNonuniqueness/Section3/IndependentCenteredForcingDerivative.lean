import EulerNonuniqueness.Section3.CenteredAntiholomorphicDerivative
import EulerNonuniqueness.Section3.ContourIndependentSymmetry
import EulerNonuniqueness.General.ComplexPairPositiveExtension

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentForcingC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def centeredForcingCircleDerivative (degree : ℕ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach

def centeredForcingCoefficientDerivative (degree : ℕ) (coefficient : ℂ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (c1ProductCLM (c1Constant coefficient)).comp
    (fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach)

theorem centeredForcingCoefficientDerivative_apply (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) :
    centeredForcingCoefficientDerivative degree coefficient direction =
      coefficient • fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach direction := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

def independentCenteredForcingDerivative (degree : ℕ) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairPositiveExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    (centeredForcingCircleDerivative degree)

theorem independentCenteredForcingDerivative_physical (degree : ℕ) (direction : PeriodicC1HolderHalf) :
    independentCenteredForcingDerivative degree (contourIndependentEmbedding direction) =
      (fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach direction, 0) := by
  unfold independentCenteredForcingDerivative contourIndependentEmbedding
  have result := EulerNonuniqueness.General.complexPairPositiveExtension_embedding c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
      (centeredForcingCircleDerivative degree) direction
  simpa only [centeredForcingCircleDerivative] using result

theorem independentCenteredForcingDerivative_angular (degree : ℕ) (offset : ℝ) :
    (contourIndependentShift offset).comp (independentCenteredForcingDerivative degree) =
      ((standardCircle offset)⁻¹ ^ (degree + 2)) •
        ((independentCenteredForcingDerivative degree).comp (contourIndependentShift offset)) := by
  apply EulerNonuniqueness.General.complexPair_linear_ext c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
  intro direction
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  have physical := independentCenteredForcingDerivative_physical degree direction
  unfold contourIndependentEmbedding at physical
  have physicalShift := contourIndependentShift_physical offset direction
  unfold contourIndependentEmbedding at physicalShift
  have nextPhysical := independentCenteredForcingDerivative_physical degree (normalizedContourShift offset direction)
  unfold contourIndependentEmbedding at nextPhysical
  rw [physical, physicalShift, nextPhysical, contourIndependentShift_eq_diagonal]
  apply Prod.ext
  · exact centeredAntiholomorphicForcing_derivative_normalized_shift degree offset direction
  · simp only [ContinuousLinearMap.coe_prodMap', Prod.map, Prod.smul_snd, map_zero, smul_zero]

end

end EulerNonuniqueness.Paper
