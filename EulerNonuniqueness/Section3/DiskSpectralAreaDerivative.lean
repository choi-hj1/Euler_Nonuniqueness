import EulerNonuniqueness.Section3.DiskChartedAreaSpectralConstraint
import EulerNonuniqueness.Section3.DiskPhysicalSpectralPolynomial
import EulerNonuniqueness.General.SpectralScalarAnnihilation

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskSpectralTubularArea (increment : PeriodicC1HolderHalf) : ℝ :=
  diskStationaryArea (diskSpectralTubularChart increment)

theorem diskSpectralTubularArea_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskSpectralTubularArea 0 := by
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskStationaryArea
      (diskSpectralTubularChart 0) := by
    rw [diskSpectralTubularChart_zero]
    exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskStationaryArea_analyticAt 0)
  unfold diskSpectralTubularArea
  with_reducible exact outer.comp diskSpectralTubularChart_hasLipschitzDerivativeNear

theorem diskSpectralTubularArea_hasFDerivAt_zero :
    HasFDerivAt diskSpectralTubularArea ((2 * Real.pi) • diskRadialMeanCLM) 0 := by
  have outer := diskStationaryArea_hasFDerivAt_zero
  rw [← diskSpectralTubularChart_zero] at outer
  have inner : HasFDerivAt diskSpectralTubularChart (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) 0 := by
    with_reducible
      exact HasStrictFDerivAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
        diskSpectralTubularChart_hasStrictFDerivAt_zero
  have actual : HasFDerivAt (fun value => diskStationaryArea (diskSpectralTubularChart value))
      (((2 * Real.pi) • diskRadialMeanCLM).comp (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf)) 0 := by
    with_reducible
      simpa only [Function.comp_def] using HasFDerivAt.comp (𝕜 := ℝ)
        (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (G := ℝ)
        (f := diskSpectralTubularChart) (g := diskStationaryArea) 0 outer inner
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, diskSpectralTubularArea] using actual

theorem diskSpectralTubularArea_eventually_stationary_transverse_derivative_zero :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∀ direction : PeriodicC1HolderHalf,
      fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment)
        (diskPhysicalTransverseProjection direction) = 0 := by
  filter_upwards [diskStationaryArea_eventually_derivative_annihilates_neutral_operator,
    diskChartedSpectralCoordinates_eventually_conjugacy,
    diskSpectralTubularChart_eventually_stationary_derivative] with increment annihilates conjugacy chartDerivative direction
  obtain ⟨coordinates, coefficientIdentity, intertwines⟩ := conjugacy
  rw [← coefficientIdentity] at intertwines
  have scalarRegular := (diskStationaryArea_analyticAt (diskRelabelNeutralCLM increment)).differentiableAt
  have scalarDerivative : HasFDerivAt diskStationaryArea
      (fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment))
      (diskSpectralTubularChart (diskRelabelNeutralCLM increment)) := by
    rw [diskSpectralTubularChart_stationary]
    with_reducible
      exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ) scalarRegular
  have composition : HasFDerivAt diskSpectralTubularArea
      ((fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)).comp
        (diskChartedSpectralCoordinates increment)) (diskRelabelNeutralCLM increment) := by
    unfold diskSpectralTubularArea
    with_reducible
      simpa only [Function.comp_def] using HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (G := ℝ)
        (f := diskSpectralTubularChart) (g := diskStationaryArea) (diskRelabelNeutralCLM increment)
        scalarDerivative chartDerivative
  have compositionIdentity : fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM increment) =
      (fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)).comp
        (diskChartedSpectralCoordinates increment) := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ) composition
  rw [compositionIdentity]
  change fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)
    (diskChartedSpectralCoordinates increment (diskPhysicalTransverseProjection direction)) = 0
  let scalar : PeriodicC1HolderHalf →L[ℝ] ℝ := fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)
  with_reducible
    exact EulerNonuniqueness.General.scalar_annihilates_intertwined_spectral_projection
      (Space := PeriodicC1HolderHalf) scalar (diskChartedNeutralOperator increment) diskRotatingDerivative
      (diskChartedSpectralCoordinates increment) diskPhysicalTransverseProjection
      diskPhysicalTransverseProjection_eq_cubicSpectralProjection intertwines annihilates direction

end

end EulerNonuniqueness.Paper
