import EulerNonuniqueness.General.ComplexPairPositiveBounds
import EulerNonuniqueness.Section3.MovingStrainGeneratorRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] movingStrainGeneratorC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentCentroidStrainDerivativeAt_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear independentCentroidStrainDerivativeAt standardCircleBanach := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by norm_num
  have derivativeRegular : EulerNonuniqueness.General.LipschitzNear
      (fderiv ℝ centroidCenteredStrain) standardCircleBanach :=
    EulerNonuniqueness.General.lipschitzNear_of_analyticAt
      (centroidCenteredStrain_analyticAt standardCircleBanach small).fderiv
  have outer := EulerNonuniqueness.General.complexPairPositiveExtension_lipschitz
    c1ConjugateCLM c1ConjugateCLM_complex_smul
  have outerRegular : EulerNonuniqueness.General.LipschitzNear
      (EulerNonuniqueness.General.complexPairPositiveExtension c1ConjugateCLM c1ConjugateCLM_complex_smul)
      (fderiv ℝ centroidCenteredStrain standardCircleBanach) :=
    ⟨_, Set.univ, Filter.univ_mem, outer.lipschitzOnWith⟩
  exact outerRegular.comp derivativeRegular

end EulerNonuniqueness.Paper
