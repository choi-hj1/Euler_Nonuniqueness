import EulerNonuniqueness.General.SpectralTubularChart
import EulerNonuniqueness.General.ContinuousCoefficientJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def spectralTubularStationarySecond (projection : Space →L[ℝ] Space)
    (operator : Space → Space →L[ℝ] Space) (point : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  fderiv ℝ operator point + (fderiv ℝ operator point).flip.comp (ContinuousLinearMap.id ℝ Space - projection)

theorem spectralTubularChart_fderiv_of_fixes
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (point : Space)
    (regular : DifferentiableAt ℝ operator point)
    (fixes : (operator point).comp projection = projection) :
    fderiv ℝ (spectralTubularChart projection operator) point =
      operator point + (fderiv ℝ operator point).flip (point - projection point) := by
  have difference := (ContinuousLinearMap.id ℝ Space - projection).hasFDerivAt (x := point)
  have paired := regular.hasFDerivAt.clm_apply difference
  have actual := (projection.hasFDerivAt (x := point)).add paired
  have identity : projection + ((operator point).comp (ContinuousLinearMap.id ℝ Space - projection) +
      (fderiv ℝ operator point).flip (point - projection point)) =
      operator point + (fderiv ℝ operator point).flip (point - projection point) := by
    apply ContinuousLinearMap.ext
    intro direction
    have fixed := congrArg (fun linear : Space →L[ℝ] Space => linear direction) fixes
    change operator point (projection direction) = projection direction at fixed
    change projection direction + (operator point (direction - projection direction) + _) = _
    rw [map_sub, fixed]
    simp only [ContinuousLinearMap.add_apply]
    abel
  change HasFDerivAt (spectralTubularChart projection operator)
    (projection + ((operator point).comp (ContinuousLinearMap.id ℝ Space - projection) +
      (fderiv ℝ operator point).flip (point - projection point))) point at actual
  rw [identity] at actual
  exact actual.fderiv

theorem spectralTubularChart_hasFDerivAt_fderiv_stationary
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (point : Space)
    (neutral : projection point = point)
    (regular : ∀ᶠ current in 𝓝 point, DifferentiableAt ℝ operator current)
    (derivativeContinuous : ContinuousAt (fderiv ℝ operator) point)
    (fixes : ∀ᶠ current in 𝓝 point, (operator current).comp projection = projection) :
    HasFDerivAt (fderiv ℝ (spectralTubularChart projection operator))
      (spectralTubularStationarySecond projection operator point) point := by
  let flipOperator : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space :=
    (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).toContinuousLinearEquiv.toContinuousLinearMap
  have coefficientContinuous : ContinuousAt (fun current => (fderiv ℝ operator current).flip) point := by
    exact flipOperator.continuous.continuousAt.comp derivativeContinuous
  have relativeDerivative := (ContinuousLinearMap.id ℝ Space - projection).hasFDerivAt (x := point)
  have relativeZero : point - projection point = 0 := by rw [neutral, sub_self]
  have applied := continuous_coefficient_vanishing_factor_hasFDerivAt
    (fun current => (fderiv ℝ operator current).flip) (fun current => current - projection current)
    point (ContinuousLinearMap.id ℝ Space - projection) coefficientContinuous relativeDerivative relativeZero
  have actual := regular.self_of_nhds.hasFDerivAt.add applied
  have equality : fderiv ℝ (spectralTubularChart projection operator) =ᶠ[𝓝 point]
      (fun current => operator current + (fderiv ℝ operator current).flip (current - projection current)) := by
    filter_upwards [regular, fixes] with current currentRegular currentFixes
    exact spectralTubularChart_fderiv_of_fixes projection operator current currentRegular currentFixes
  exact actual.congr_of_eventuallyEq equality

theorem spectralTubularStationarySecond_symmetric
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (point : Space)
    (neutral : projection point = point)
    (regular : ∀ᶠ current in 𝓝 point, DifferentiableAt ℝ operator current)
    (derivativeContinuous : ContinuousAt (fderiv ℝ operator) point)
    (fixes : ∀ᶠ current in 𝓝 point, (operator current).comp projection = projection)
    (first second : Space) :
    spectralTubularStationarySecond projection operator point first second =
      spectralTubularStationarySecond projection operator point second first := by
  have firstNear : ∀ᶠ current in 𝓝 point,
      HasFDerivAt (spectralTubularChart projection operator)
        (fderiv ℝ (spectralTubularChart projection operator) current) current := by
    filter_upwards [regular] with current actual
    have paired := actual.hasFDerivAt.clm_apply
      ((ContinuousLinearMap.id ℝ Space - projection).hasFDerivAt (x := current))
    exact ((projection.hasFDerivAt (x := current)).add paired).differentiableAt.hasFDerivAt
  exact second_derivative_symmetric_of_eventually_of_real firstNear
    (spectralTubularChart_hasFDerivAt_fderiv_stationary projection operator point neutral regular
      derivativeContinuous fixes) first second

end EulerNonuniqueness.General
