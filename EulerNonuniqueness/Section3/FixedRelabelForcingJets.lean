import EulerNonuniqueness.Section3.CenteredForcingFixedRelabel
import EulerNonuniqueness.Section3.FixedRelabelDerivativeConjugacy
import EulerNonuniqueness.Section3.ContourVelocitySecondDerivativeIdentity
import EulerNonuniqueness.General.LinearEquivariantJets

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance fixedRelabelJetsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule

theorem centeredAntiholomorphicForcing_fderiv_fixedRelabel (degree : ℕ) (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    (fderiv ℝ (centeredAntiholomorphicForcing degree) (fixedRelabelEquivalence angular small data)).comp
      (fixedRelabelEquivalence angular small).toContinuousLinearMap =
      (fixedRelabelEquivalence angular small).toContinuousLinearMap.comp
        (fderiv ℝ (centeredAntiholomorphicForcing degree) data) := by
  exact EulerNonuniqueness.General.fderiv_linear_equivariant (centeredAntiholomorphicForcing degree)
    (fixedRelabelEquivalence angular small).toContinuousLinearMap data
    (centeredAntiholomorphicForcing_analyticAt degree data).differentiableAt
    (centeredAntiholomorphicForcing_analyticAt degree (fixedRelabelEquivalence angular small data)).differentiableAt
    (Filter.Eventually.of_forall (centeredAntiholomorphicForcing_fixedRelabel degree angular small))

theorem contourVelocity_hessian_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    fderiv ℝ (fderiv ℝ extendedContourVelocity) (fixedRelabelEquivalence angular angularSmall data)
      (fixedRelabelEquivalence angular angularSmall first) (fixedRelabelEquivalence angular angularSmall second) =
      fixedRelabelEquivalence angular angularSmall
        (fderiv ℝ (fderiv ℝ extendedContourVelocity) data first second) := by
  let relabel := (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap
  have firstNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((continuous_id.sub continuous_const).norm) continuous_const).mem_nhds small
  have secondNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖relabel current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    (isOpen_lt ((relabel.continuous.sub continuous_const).norm) continuous_const).mem_nhds composedSmall
  apply EulerNonuniqueness.General.second_linear_equivariant
    (fun current => fderiv ℝ extendedContourVelocity current) relabel data
    (differentiableAt_fderiv_extendedContourVelocity data small)
    (differentiableAt_fderiv_extendedContourVelocity (relabel data) composedSmall)
  filter_upwards [firstNeighborhood, secondNeighborhood] with current firstNear secondNear direction
  have identity := contourVelocity_derivative_fixedRelabelEquivalence angular angularSmall current firstNear secondNear
  exact congrArg (fun derivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => derivative direction) identity

theorem centeredForcing_linear_coefficient_fixedRelabel (degree : ℕ) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data direction primitive : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    fderiv ℝ (centeredAntiholomorphicForcing degree) (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall direction) +
      fderiv ℝ (fderiv ℝ extendedContourVelocity) (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall direction) (fixedRelabelEquivalence angular angularSmall primitive) =
    fixedRelabelEquivalence angular angularSmall
      (fderiv ℝ (centeredAntiholomorphicForcing degree) data direction +
        fderiv ℝ (fderiv ℝ extendedContourVelocity) data direction primitive) := by
  have forcing := centeredAntiholomorphicForcing_fderiv_fixedRelabel degree angular angularSmall data
  have evaluated := congrArg (fun derivative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => derivative direction) forcing
  change fderiv ℝ (centeredAntiholomorphicForcing degree) (fixedRelabelEquivalence angular angularSmall data)
      (fixedRelabelEquivalence angular angularSmall direction) =
    fixedRelabelEquivalence angular angularSmall (fderiv ℝ (centeredAntiholomorphicForcing degree) data direction) at evaluated
  rw [evaluated, contourVelocity_hessian_fixedRelabel angular angularSmall data direction primitive small composedSmall,
    map_add]

end EulerNonuniqueness.Paper
