import EulerNonuniqueness.Section3.DiskSpectralDifferentiatedIntertwining
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadratic
import EulerNonuniqueness.General.SpectralJetCoordinateCancellation
import EulerNonuniqueness.General.InverseQuadraticCoefficient

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance spectralQuadraticJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralTubularChart_eventually_stationary_quadratic_jet :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        diskChartedSpectralCoordinates point = coordinates.toContinuousLinearMap ∧
        ∀ direction correction : PeriodicC1HolderHalf, diskRelabelNeutralCLM direction = 0 →
          EulerNonuniqueness.General.coordinateQuadraticJet coordinates
              (diskSpectralTubularStationarySecond point)
              (fderiv ℝ diskChartedEulerField point)
              (fderiv ℝ (fderiv ℝ diskChartedEulerField) point) direction correction =
            coordinates.symm (fderiv ℝ (fderiv ℝ diskChartedEulerField) point
              (coordinates direction) (coordinates (correction - diskRelabelNeutralCLM correction))) := by
  filter_upwards [diskChartedSpectralCoordinates_eventually_conjugacy,
    diskChartedSpectralCoordinates_eventually_fixes_relabel,
    diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.1,
    diskChartedEulerField_eventually_twice_differentiable.eventually_nhds,
    diskChartedSpectralCoordinates_eventually_differentiated_intertwining]
    with point conjugacy fixes coordinatesRegular fieldRegular differentiated neutral
  obtain ⟨coordinates, coordinateIdentity, intertwines⟩ := conjugacy
  refine ⟨coordinates, coordinateIdentity, ?_⟩
  have derivativeFactors : (fderiv ℝ diskChartedSpectralCoordinates point).comp diskRelabelNeutralCLM =
      fderiv ℝ diskChartedSpectralCoordinates point := by
    with_reducible
      exact EulerNonuniqueness.General.operator_derivative_factors_projection
        diskRelabelNeutralCLM diskChartedSpectralCoordinates point _
        diskChartedSpectralCoordinates_neutral_parameter neutral coordinatesRegular.hasFDerivAt
  have factors (direction : PeriodicC1HolderHalf) :
      fderiv ℝ diskChartedSpectralCoordinates point (diskRelabelNeutralCLM direction) =
        fderiv ℝ diskChartedSpectralCoordinates point direction :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
      linear direction) derivativeFactors
  have coordinatesFix (direction : PeriodicC1HolderHalf) :
      coordinates (diskRelabelNeutralCLM direction) = diskRelabelNeutralCLM direction := by
    simpa only [coordinateIdentity, ContinuousLinearEquiv.coe_coe] using fixes direction
  have actualIntertwining (direction : PeriodicC1HolderHalf) :
      fderiv ℝ diskChartedEulerField point (coordinates direction) =
        coordinates (diskRotatingDerivative direction) := by
    have applied := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear direction) intertwines
    simpa only [ContinuousLinearMap.comp_apply, diskChartedNeutralOperator, neutral] using applied
  have firstNear := fieldRegular.mono (fun _ regular => regular.1.hasFDerivAt)
  have secondActual := fieldRegular.self_of_nhds.2.hasFDerivAt
  have symmetric (first second : PeriodicC1HolderHalf) :
      fderiv ℝ (fderiv ℝ diskChartedEulerField) point first second =
        fderiv ℝ (fderiv ℝ diskChartedEulerField) point second first := by
    with_reducible
      exact second_derivative_symmetric_of_eventually_of_real firstNear secondActual first second
  have differentiatedActual (parameterDirection direction : PeriodicC1HolderHalf) :
      fderiv ℝ (fderiv ℝ diskChartedEulerField) point (diskRelabelNeutralCLM parameterDirection)
          (coordinates direction) +
        fderiv ℝ diskChartedEulerField point
          (fderiv ℝ diskChartedSpectralCoordinates point parameterDirection direction) =
      fderiv ℝ diskChartedSpectralCoordinates point parameterDirection (diskRotatingDerivative direction) := by
    simpa only [coordinateIdentity, ContinuousLinearEquiv.coe_coe] using
      differentiated neutral parameterDirection direction
  intro direction correction transverse
  let originalGenerator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskChartedEulerField point
  let originalSecond : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ (fderiv ℝ diskChartedEulerField) point
  let differential : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskChartedSpectralCoordinates point
  have kernel := diskRelabelNeutralCLM_rotatingDerivative_zero
  have actual : EulerNonuniqueness.General.coordinateQuadraticJet coordinates
      (diskSpectralTubularStationarySecond point)
      (fderiv ℝ diskChartedEulerField point)
      (fderiv ℝ (fderiv ℝ diskChartedEulerField) point) direction correction =
      coordinates.symm (fderiv ℝ (fderiv ℝ diskChartedEulerField) point
        (coordinates direction) (coordinates (correction - diskRelabelNeutralCLM correction))) := by
    unfold diskSpectralTubularStationarySecond EulerNonuniqueness.General.spectralTubularStationarySecond
    with_reducible_and_instances
      exact @EulerNonuniqueness.General.coordinateQuadraticJet_spectral_transverse
        PeriodicC1HolderHalf spectralQuadraticJetC1Group chartedBilinearC1Space
        diskRelabelNeutralCLM diskRotatingDerivative originalGenerator
        coordinates differential originalSecond factors coordinatesFix
        kernel actualIntertwining symmetric
        differentiatedActual direction correction transverse
  exact actual

end EulerNonuniqueness.Paper
