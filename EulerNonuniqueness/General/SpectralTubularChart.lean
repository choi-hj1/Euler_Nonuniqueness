import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def spectralTubularChart (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (value : Space) : Space := projection value + operator value (value - projection value)

theorem spectralTubularChart_hasLipschitzDerivativeNear
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (regular : HasLipschitzDerivativeNear operator (0 : Space)) :
    HasLipschitzDerivativeNear (spectralTubularChart projection operator) (0 : Space) := by
  have linearRegular := hasLipschitzDerivativeNear_continuousLinearMap projection (0 : Space)
  have identityRegular := hasLipschitzDerivativeNear_continuousLinearMap (ContinuousLinearMap.id ℝ Space) (0 : Space)
  exact linearRegular.add (HasLipschitzDerivativeNear.bilinear
    (ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)) regular (identityRegular.sub linearRegular))

theorem spectralTubularChart_zero (projection : Space →L[ℝ] Space)
    (operator : Space → Space →L[ℝ] Space) : spectralTubularChart projection operator 0 = 0 := by
  simp [spectralTubularChart]

theorem spectralTubularChart_hasStrictFDerivAt_zero
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (regular : HasLipschitzDerivativeNear operator (0 : Space))
    (atZero : operator 0 = ContinuousLinearMap.id ℝ Space) :
    HasStrictFDerivAt (spectralTubularChart projection operator) (ContinuousLinearMap.id ℝ Space) 0 := by
  have linear := (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Space) (F := Space) projection (x := (0 : Space)))
  have difference := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Space) (F := Space)
    (ContinuousLinearMap.id ℝ Space - projection) (x := (0 : Space))
  have paired := regular.hasStrictFDerivAt.clm_apply difference
  have actual := linear.add paired
  have operatorIdentity : projection + (ContinuousLinearMap.id ℝ Space - projection) =
      ContinuousLinearMap.id ℝ Space := by abel
  simpa only [map_zero, sub_self, atZero, ContinuousLinearMap.flip_apply,
    map_zero, zero_add, add_zero, ContinuousLinearMap.id_comp, operatorIdentity,
    spectralTubularChart, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] using actual

theorem spectralTubularChart_stationary
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (value : Space)
    (idempotent : projection (projection value) = projection value) :
    spectralTubularChart projection operator (projection value) = projection value := by
  simp only [spectralTubularChart, idempotent, sub_self, map_zero, add_zero]

theorem spectralTubularChart_hasFDerivAt_stationary
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (value : Space)
    (differential : Space →L[ℝ] Space →L[ℝ] Space)
    (actualOperator : HasFDerivAt operator differential (projection value))
    (idempotent : projection (projection value) = projection value)
    (fixes : (operator (projection value)).comp projection = projection) :
    HasFDerivAt (spectralTubularChart projection operator) (operator (projection value)) (projection value) := by
  have difference := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Space) (F := Space)
    (ContinuousLinearMap.id ℝ Space - projection) (x := projection value)
  have paired := actualOperator.clm_apply difference
  have actual := (projection.hasFDerivAt (x := projection value)).add paired
  have zero : (ContinuousLinearMap.id ℝ Space - projection) (projection value) = 0 := by
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, idempotent, sub_self]
  simp only [zero, ContinuousLinearMap.flip_apply, map_zero, add_zero] at actual
  have derivativeIdentity : projection + (operator (projection value)).comp (ContinuousLinearMap.id ℝ Space - projection) =
      operator (projection value) := by
    apply ContinuousLinearMap.ext
    intro direction
    have fixed := congrArg (fun linear : Space →L[ℝ] Space => linear direction) fixes
    change projection direction + operator (projection value) (direction - projection direction) = _
    change operator (projection value) (projection direction) = projection direction at fixed
    rw [map_sub, fixed]
    abel
  rw [derivativeIdentity] at actual
  exact actual

theorem spectralTubularChart_hasFDerivAt_stationary_of_differentiable
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (value : Space)
    (regular : DifferentiableAt ℝ operator (projection value))
    (idempotent : projection (projection value) = projection value)
    (fixes : (operator (projection value)).comp projection = projection) :
    HasFDerivAt (spectralTubularChart projection operator) (operator (projection value)) (projection value) :=
  spectralTubularChart_hasFDerivAt_stationary projection operator value
    (fderiv ℝ operator (projection value)) regular.hasFDerivAt idempotent fixes

end

end EulerNonuniqueness.General
