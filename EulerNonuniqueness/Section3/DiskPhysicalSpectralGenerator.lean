import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseJacobian
import EulerNonuniqueness.Section3.DiskSpectralFiberAlgebra
import EulerNonuniqueness.General.IntertwinedNeutralRange

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralGeneratorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralChart_stationary_relabel (point : PeriodicC1HolderHalf)
    (neutral : diskRelabelNeutralCLM point = point) :
    diskPhysicalSpectralChart point = diskRelabelCurve (diskNeutralCLM point) 1 := by
  have tubular := diskSpectralTubularChart_stationary point
  rw [neutral] at tubular
  rw [diskPhysicalSpectralChart, tubular]
  calc
    diskStationaryChart point = diskStationaryChart (diskRelabelNeutralCLM point) := congrArg diskStationaryChart neutral.symm
    _ = diskRelabelCurve (diskNeutralCLM point) 1 := by
      rw [diskRelabelNeutralCLM_apply, diskStationaryChart_relabel _ (diskNeutralCLM_real point)]

theorem diskPhysicalSpectralChart_eventually_generator_equivalence :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        HasFDerivAt diskPhysicalSpectralChart coordinates.toContinuousLinearMap point ∧
        diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point) = coordinates.symm.toContinuousLinearMap ∧
        ∀ direction : PeriodicC1HolderHalf,
          relabeledDiskDerivative (diskNeutralCLM point) (coordinates direction) =
            coordinates (diskRotatingDerivative direction) := by
  have near : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskStationaryChart point - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)) := by
    have limit : Tendsto diskStationaryChart (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 standardCircleBanach) := by
      simpa only [diskStationaryChart_zero] using (diskStationaryChart_analyticAt 0).continuousAt.tendsto
    simpa only [Metric.mem_ball, dist_eq_norm] using limit.eventually
      (Metric.ball_mem_nhds standardCircleBanach
        (show (0 : ℝ) < min (1 / 3) (2 / (3 * Real.pi)) by positivity))
  filter_upwards [diskStationaryChart_eventually_jacobian_equivalence,
    diskChartedSpectralCoordinates_eventually_conjugacy,
    diskSpectralTubularChart_eventually_stationary_derivative,
    diskPhysicalSpectralInverseDerivative_eventually_jacobian_identity, near]
    with point stationaryJacobian spectralJacobian tubularDerivative inverseIdentity close neutral
  obtain ⟨stationaryCoordinates, stationaryDerivative, stationaryInverse, stationaryInverseActual⟩ := stationaryJacobian
  obtain ⟨spectralCoordinates, spectralIdentity, spectralIntertwining⟩ := spectralJacobian
  have stationaryShape : diskStationaryChart point = diskRelabelCurve (diskNeutralCLM point) 1 := by
    have identity := diskPhysicalSpectralChart_stationary_relabel point neutral
    have tubular := diskSpectralTubularChart_stationary point
    rw [neutral] at tubular
    simpa only [diskPhysicalSpectralChart, tubular] using identity
  have rawNear : ‖diskRelabelCurve (diskNeutralCLM point) 1 - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi)) := by
    rw [← stationaryShape]
    exact lt_min ((close.trans_le (min_le_left _ _)).trans (by norm_num : (1 / 3 : ℝ) < 1))
      (close.trans_le (min_le_right _ _))
  have rawDerivative := diskEulerRotatingField_hasFDerivAt_relabel (diskNeutralCLM point) rawNear
  have stationary := diskEulerRotatingField_relabel_zero (diskNeutralCLM point) (diskNeutralCLM_real point)
    (by simpa only [← stationaryShape] using close.trans_le (min_le_left _ _))
    (by simpa only [← stationaryShape] using close.trans_le (min_le_right _ _))
  rw [← stationaryShape] at rawDerivative stationary
  let inverseLinear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskChartInverseDerivative point
  have stationaryIntertwining :
      (relabeledDiskDerivative (diskNeutralCLM point)).comp stationaryCoordinates.toContinuousLinearMap =
        stationaryCoordinates.toContinuousLinearMap.comp (fderiv ℝ diskChartedEulerField point) := by
    unfold diskChartedEulerField
    with_reducible
      exact EulerNonuniqueness.General.equilibrium_chart_derivative_intertwines
        diskEulerRotatingField diskStationaryChart diskChartInverseDerivative point
        (relabeledDiskDerivative (diskNeutralCLM point)) stationaryCoordinates inverseLinear
        rawDerivative stationaryDerivative stationaryInverseActual stationaryInverse stationary
  have tubularActual := tubularDerivative
  rw [neutral, spectralIdentity] at tubularActual
  have tubularIdentity : diskSpectralTubularChart point = point := by
    simpa only [neutral] using diskSpectralTubularChart_stationary point
  have stationaryAtTubular : HasFDerivAt diskStationaryChart stationaryCoordinates.toContinuousLinearMap
      (diskSpectralTubularChart point) := by rw [tubularIdentity]; exact stationaryDerivative
  let coordinates := spectralCoordinates.trans stationaryCoordinates
  have fullDerivative : HasFDerivAt diskPhysicalSpectralChart coordinates.toContinuousLinearMap point := by
    have actual := stationaryAtTubular.comp point tubularActual
    exact actual
  refine ⟨coordinates, fullDerivative, inverseIdentity coordinates fullDerivative, ?_⟩
  intro direction
  have first := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    linear (spectralCoordinates direction)) stationaryIntertwining
  have second := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    linear direction) spectralIntertwining
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at first second
  simp only [diskChartedNeutralOperator, neutral] at second
  change relabeledDiskDerivative (diskNeutralCLM point) (stationaryCoordinates (spectralCoordinates direction)) =
    stationaryCoordinates (spectralCoordinates (diskRotatingDerivative direction))
  rw [first, second]

end EulerNonuniqueness.Paper
