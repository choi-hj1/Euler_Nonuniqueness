import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus
import EulerNonuniqueness.Section3.ComplexOperatorRestriction

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℂ Space] [NormedSpace ℝ Space] [IsScalarTower ℝ ℂ Space]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target] [NormedSpace ℝ Target] [IsScalarTower ℝ ℂ Target]

theorem hasLipschitzDerivativeNear_of_complex {function : Space → Target} {point : Space}
    (differentiable : ∀ᶠ current in 𝓝 point, DifferentiableAt ℂ function current)
    (derivativeLip : LipschitzNear (fderiv ℂ function) point) :
    HasLipschitzDerivativeNear function point := by
  constructor
  · exact differentiable.mono fun current regular => regular.restrictScalars ℝ
  · have restriction : LipschitzNear
        (fun operator : Space →L[ℂ] Target => operator.restrictScalars ℝ) (fderiv ℂ function point) :=
      lipschitzNear_of_contDiffAt_one
        (ContinuousLinearMap.restrictScalarsL ℂ Space Target ℝ ℝ).contDiff.contDiffAt
    have equality : fderiv ℝ function =ᶠ[𝓝 point]
        (fun current => (fderiv ℂ function current).restrictScalars ℝ) := by
      filter_upwards [differentiable] with current regular
      exact (regular.hasFDerivAt.restrictScalars ℝ).fderiv
    exact (LipschitzNear.comp
      (outer := fun operator : Space →L[ℂ] Target => operator.restrictScalars ℝ)
      (inner := fderiv ℂ function) restriction derivativeLip).congr equality

variable {First Second Range : Type*}
  [NormedAddCommGroup First] [NormedSpace ℂ First] [NormedSpace ℝ First] [IsScalarTower ℝ ℂ First]
  [NormedAddCommGroup Second] [NormedSpace ℂ Second] [NormedSpace ℝ Second] [IsScalarTower ℝ ℂ Second]
  [NormedAddCommGroup Range] [NormedSpace ℂ Range] [NormedSpace ℝ Range] [IsScalarTower ℝ ℂ Range]

def complexBilinearRestrictionCLM :
    (First →L[ℂ] Second →L[ℂ] Range) →L[ℝ] First →L[ℝ] Second →L[ℝ] Range :=
  ((ContinuousLinearMap.compL ℝ First (Second →L[ℂ] Range) (Second →L[ℝ] Range))
      (ContinuousLinearMap.restrictScalarsL ℂ Second Range ℝ ℝ)).comp
    (ContinuousLinearMap.restrictScalarsL ℂ First (Second →L[ℂ] Range) ℝ ℝ)

theorem complexBilinearRestrictionCLM_apply (operator : First →L[ℂ] Second →L[ℂ] Range) :
    complexBilinearRestrictionCLM operator = operator.bilinearRestrictScalars ℝ := rfl

end

end EulerNonuniqueness.General
