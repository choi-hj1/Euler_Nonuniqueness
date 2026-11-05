import EulerNonuniqueness.General.BilinearOperatorCalculus
import Mathlib.Analysis.Calculus.FDeriv.Comp

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def compositionSecondJet (outerLinear innerLinear : Space →L[ℝ] Space)
    (outerSecond innerSecond : BilinearEnd Space) : BilinearEnd Space :=
  outerSecond.bilinearComp innerLinear innerLinear + bilinearPostcompose outerLinear innerSecond

theorem hasFDerivAt_fderiv_composition
    (outer inner : Space → Space) (base : Space)
    (outerLinear innerLinear : Space →L[ℝ] Space) (outerSecond innerSecond : BilinearEnd Space)
    (outerFirst : ∀ᶠ point in 𝓝 (inner base), DifferentiableAt ℝ outer point)
    (innerFirst : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ inner point)
    (outerDerivative : HasFDerivAt outer outerLinear (inner base))
    (innerDerivative : HasFDerivAt inner innerLinear base)
    (outerSecondDerivative : HasFDerivAt (fderiv ℝ outer) outerSecond (inner base))
    (innerSecondDerivative : HasFDerivAt (fderiv ℝ inner) innerSecond base) :
    HasFDerivAt (fderiv ℝ (fun point => outer (inner point)))
      (compositionSecondJet outerLinear innerLinear outerSecond innerSecond) base := by
  have outerComposed := outerSecondDerivative.comp base innerDerivative
  have expression := outerComposed.clm_comp innerSecondDerivative
  simp only [Function.comp_def] at expression
  have derivativeIdentity :
      (ContinuousLinearMap.compL ℝ Space Space Space (fderiv ℝ outer (inner base))).comp innerSecond +
          ((ContinuousLinearMap.compL ℝ Space Space Space).flip (fderiv ℝ inner base)).comp
            (outerSecond.comp innerLinear) =
        compositionSecondJet outerLinear innerLinear outerSecond innerSecond := by
    rw [outerDerivative.fderiv, innerDerivative.fderiv]
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [compositionSecondJet, bilinearPostcompose, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearComp_apply]
    exact add_comm _ _
  rw [derivativeIdentity] at expression
  apply expression.congr_of_eventuallyEq
  filter_upwards [innerFirst, innerDerivative.continuousAt.eventually outerFirst]
    with point innerRegular outerRegular
  exact fderiv_comp point outerRegular innerRegular

theorem compositionSecondJet_symmetric
    (outerLinear innerLinear : Space →L[ℝ] Space) (outerSecond innerSecond : BilinearEnd Space)
    (outerSymmetric : ∀ first second, outerSecond first second = outerSecond second first)
    (innerSymmetric : ∀ first second, innerSecond first second = innerSecond second first)
    (first second : Space) :
    compositionSecondJet outerLinear innerLinear outerSecond innerSecond first second =
      compositionSecondJet outerLinear innerLinear outerSecond innerSecond second first := by
  simp only [compositionSecondJet, bilinearPostcompose, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]
  rw [outerSymmetric, innerSymmetric]

end EulerNonuniqueness.General
