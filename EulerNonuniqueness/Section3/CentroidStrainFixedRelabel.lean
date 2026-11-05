import EulerNonuniqueness.Section3.CenteredForcingFixedRelabel
import EulerNonuniqueness.Section3.CentroidCenteredStrainJet
import EulerNonuniqueness.General.LinearEquivariantJets

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centroidStrainRelabelC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace

open Filter
open scoped Topology

theorem contourCentroidFunctional_fixedRelabel (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    contourCentroidFunctional (fixedRelabelEquivalence angular small data) = contourCentroidFunctional data := by
  unfold contourCentroidFunctional
  rw [contourPolynomialMoment_fixedRelabel, contourAreaFunctional_fixedRelabel]

theorem centroidCenteredStrain_fixedRelabel (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    centroidCenteredStrain (fixedRelabelEquivalence angular small data) =
      fixedRelabelEquivalence angular small (centroidCenteredStrain data) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [fixedRelabelEquivalence_value]
  change star ((fixedRelabelEquivalence angular small data).val.1 label) -
      star (contourCentroidFunctional (fixedRelabelEquivalence angular small data)) =
    star (data.val.1 (periodicLabelShift angular label)) - star (contourCentroidFunctional data)
  rw [fixedRelabelEquivalence_value, contourCentroidFunctional_fixedRelabel]

theorem centroidCenteredStrain_analyticAt (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    AnalyticAt ℝ centroidCenteredStrain data := by
  have conjugate := ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).analyticAt
    (x := contourCentroidFunctional data)).comp
    (f := contourCentroidFunctional) (analyticAt_contourCentroidFunctional data small)
  have constant := (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := ℂ)
    (F := PeriodicC1HolderHalf) c1ConstantCLM (star (contourCentroidFunctional data))).comp
    (f := fun current => star (contourCentroidFunctional current)) conjugate
  exact (c1ConjugateCLM.analyticAt data).sub constant

theorem centroidCenteredStrain_derivative_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ centroidCenteredStrain (fixedRelabelEquivalence angular angularSmall data)).comp
        (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap =
      (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.comp
        (fderiv ℝ centroidCenteredStrain data) := by
  apply EulerNonuniqueness.General.fderiv_linear_equivariant centroidCenteredStrain
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap data
    (centroidCenteredStrain_analyticAt data small).differentiableAt
    (centroidCenteredStrain_analyticAt _ composedSmall).differentiableAt
  exact Filter.Eventually.of_forall (centroidCenteredStrain_fixedRelabel angular angularSmall)

theorem contourCentroidFunctional_derivative_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ contourCentroidFunctional (fixedRelabelEquivalence angular angularSmall data)).comp
        (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap =
      fderiv ℝ contourCentroidFunctional data := by
  have image := (analyticAt_contourCentroidFunctional
    (fixedRelabelEquivalence angular angularSmall data) composedSmall).differentiableAt.hasFDerivAt
  have source := (analyticAt_contourCentroidFunctional data small).differentiableAt.hasFDerivAt
  have composed := image.comp data (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.hasFDerivAt
  change HasFDerivAt (fun current => contourCentroidFunctional (fixedRelabelEquivalence angular angularSmall current)) _ _ at composed
  have identity : (fun current => contourCentroidFunctional (fixedRelabelEquivalence angular angularSmall current)) =
      contourCentroidFunctional := funext (contourCentroidFunctional_fixedRelabel angular angularSmall)
  rw [identity] at composed
  exact composed.unique source

theorem contourCentroidFunctional_tangent_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < 1 / 3) :
    fderiv ℝ contourCentroidFunctional (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall direction) = 0 ↔
      fderiv ℝ contourCentroidFunctional data direction = 0 := by
  have identity := congrArg (fun derivative : PeriodicC1HolderHalf →L[ℝ] ℂ => derivative direction)
    (contourCentroidFunctional_derivative_fixedRelabel angular angularSmall data small composedSmall)
  change fderiv ℝ contourCentroidFunctional (fixedRelabelEquivalence angular angularSmall data)
    (fixedRelabelEquivalence angular angularSmall direction) = _ at identity
  rw [identity]

end EulerNonuniqueness.Paper
