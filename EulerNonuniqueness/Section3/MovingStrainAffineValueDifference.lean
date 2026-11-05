import EulerNonuniqueness.Section3.MovingStrainAffineTaylorIdentity
import EulerNonuniqueness.General.RelativeRemainderRecombination

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainAffineResidual_pair_norm_le
    (initialAngular finalAngular : PeriodicC1HolderHalf)
    (initialSmall : ‖initialAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2)
    (initialNearby : ‖fixedRelabelEquivalence initialAngular initialSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (finalNearby : ‖fixedRelabelEquivalence finalAngular finalSmall standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi))))
    (coefficient : ℂ) (initialIncrement finalIncrement : PeriodicC1HolderHalf) :
    let initialBase := fixedRelabelEquivalence initialAngular initialSmall standardCircleBanach
    let finalBase := fixedRelabelEquivalence finalAngular finalSmall standardCircleBanach
    ‖movingStrainAffineResidual initialBase coefficient (initialBase + initialIncrement) -
      movingStrainAffineResidual finalBase coefficient (finalBase + finalIncrement)‖ ≤
    ‖movingStrainAffineLinearResidualCLM initialBase coefficient initialIncrement -
      movingStrainAffineLinearResidualCLM finalBase coefficient finalIncrement‖ +
    ‖movingStrainAffineTaylorRemainder initialBase coefficient initialIncrement -
      movingStrainAffineTaylorRemainder finalBase coefficient finalIncrement‖ := by
  intro initialBase finalBase
  have first := movingStrainAffineResidual_eq_linear_add_taylor
    initialAngular initialSmall initialNearby coefficient initialIncrement
  have second := movingStrainAffineResidual_eq_linear_add_taylor
    finalAngular finalSmall finalNearby coefficient finalIncrement
  let firstValue : PeriodicC1HolderHalf := movingStrainAffineResidual initialBase coefficient (initialBase + initialIncrement)
  let finalValue : PeriodicC1HolderHalf := movingStrainAffineResidual finalBase coefficient (finalBase + finalIncrement)
  let firstLinear : PeriodicC1HolderHalf := movingStrainAffineLinearResidualCLM initialBase coefficient initialIncrement
  let finalLinear : PeriodicC1HolderHalf := movingStrainAffineLinearResidualCLM finalBase coefficient finalIncrement
  let firstTaylor : PeriodicC1HolderHalf := movingStrainAffineTaylorRemainder initialBase coefficient initialIncrement
  let finalTaylor : PeriodicC1HolderHalf := movingStrainAffineTaylorRemainder finalBase coefficient finalIncrement
  with_reducible_and_instances
    exact EulerNonuniqueness.General.norm_residual_difference_le_of_linear_taylor
      (Space := PeriodicC1HolderHalf) firstValue finalValue firstLinear finalLinear firstTaylor finalTaylor first second

end EulerNonuniqueness.Paper
