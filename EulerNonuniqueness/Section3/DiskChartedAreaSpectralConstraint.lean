import EulerNonuniqueness.Section3.FixedRelabelAreaDerivative
import EulerNonuniqueness.General.EquilibriumChartScalarConstraint

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule neutralStationarityContinuousNeg neutralStationarityContinuousSub

theorem diskStationaryArea_relabel_derivative_annihilates
    (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (angularSmall : ‖angular‖ < 1 / 2)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3)
    (chordSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf)
    (chartDerivative : HasFDerivAt diskStationaryChart coordinates.toContinuousLinearMap (diskMaterialPerturbation 0 angular))
    (inverseIdentity : diskChartInverseDerivative (diskMaterialPerturbation 0 angular) = coordinates.symm.toContinuousLinearMap)
    (inverseActual : HasFDerivAt diskChartInverseDerivative
      (fderiv ℝ diskChartInverseDerivative (diskMaterialPerturbation 0 angular)) (diskMaterialPerturbation 0 angular))
    (direction : PeriodicC1HolderHalf) :
    fderiv ℝ diskStationaryArea (diskMaterialPerturbation 0 angular)
      (fderiv ℝ diskChartedEulerField (diskMaterialPerturbation 0 angular) direction) = 0 := by
  have near : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    lt_min (small.trans (by norm_num)) chordSmall
  have fieldDerivative := diskEulerRotatingField_hasFDerivAt_relabel angular near
  have equilibrium := diskEulerRotatingField_relabel_zero angular realValues small chordSmall
  have scalarRegular := (analyticAt_contourAreaFunctional
    (diskStationaryChart (diskMaterialPerturbation 0 angular))).differentiableAt
  have annihilates : ∀ value, fderiv ℝ contourAreaFunctional
      (diskStationaryChart (diskMaterialPerturbation 0 angular)) (relabeledDiskDerivative angular value) = 0 := by
    rw [diskStationaryChart_relabel angular realValues]
    exact contourAreaFunctional_fderiv_relabel_rotatingDerivative_zero angular angularSmall realValues near
  rw [← diskStationaryChart_relabel angular realValues] at fieldDerivative equilibrium
  let inverseLinear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskChartInverseDerivative (diskMaterialPerturbation 0 angular)
  unfold diskStationaryArea diskChartedEulerField
  with_reducible
    exact EulerNonuniqueness.General.equilibrium_chart_scalar_derivative_annihilates
      (Space := PeriodicC1HolderHalf) diskEulerRotatingField diskStationaryChart diskChartInverseDerivative
      contourAreaFunctional (diskMaterialPerturbation 0 angular) (relabeledDiskDerivative angular) coordinates
      inverseLinear fieldDerivative chartDerivative inverseActual inverseIdentity equilibrium scalarRegular annihilates direction

theorem diskStationaryArea_eventually_derivative_annihilates_neutral_operator :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf), ∀ direction : PeriodicC1HolderHalf,
      fderiv ℝ diskStationaryArea (diskRelabelNeutralCLM increment)
        (diskChartedNeutralOperator increment direction) = 0 := by
  have neutralLimit : Tendsto diskRelabelNeutralCLM (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 0) := by
    simpa only [map_zero] using diskRelabelNeutralCLM.continuous.tendsto (0 : PeriodicC1HolderHalf)
  have angularLimit : Tendsto (fun increment => ‖diskNeutralCLM increment‖)
      (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
    have angularContinuous : Continuous (fun increment : PeriodicC1HolderHalf => ‖diskNeutralCLM increment‖) := by
      with_reducible exact Continuous.norm (E := PeriodicC1HolderHalf) diskNeutralCLM.continuous
    have zeroNorm : ‖(0 : PeriodicC1HolderHalf)‖ = 0 := by
      change max ‖(0 : BoundedContinuousFunction ℝ ℂ)‖ ‖(0 : PeriodicHolderHalf)‖ = 0
      simp
    simpa only [map_zero, zeroNorm] using angularContinuous.tendsto (0 : PeriodicC1HolderHalf)
  have chartLimit : Tendsto (fun increment =>
      ‖diskStationaryChart (diskRelabelNeutralCLM increment) - standardCircleBanach‖)
      (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 (0 : ℝ)) := by
    have actual := (((diskStationaryChart_analyticAt 0).continuousAt.tendsto.comp neutralLimit).sub
      (tendsto_const_nhds (x := standardCircleBanach))).norm
    simpa [Function.comp_def, diskStationaryChart_zero] using actual
  have close := chartLimit.eventually (eventually_lt_nhds
    (lt_min (by norm_num : (0 : ℝ) < 1 / 3) (by positivity : 0 < 2 / (3 * Real.pi))))
  have angularClose := angularLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [neutralLimit.eventually diskStationaryChart_eventually_jacobian_equivalence,
    close, angularClose] with increment jacobian near angularSmall direction
  obtain ⟨coordinates, chartDerivative, inverseIdentity, inverseActual⟩ := jacobian
  have identity := diskRelabelNeutralCLM_apply increment
  unfold diskChartedNeutralOperator
  rw [identity] at chartDerivative inverseIdentity inverseActual ⊢
  rw [identity, diskStationaryChart_relabel _ (diskNeutralCLM_real increment)] at near
  exact diskStationaryArea_relabel_derivative_annihilates (diskNeutralCLM increment) (diskNeutralCLM_real increment)
    angularSmall (near.trans_le (min_le_left _ _)) (near.trans_le (min_le_right _ _))
    coordinates chartDerivative inverseIdentity inverseActual direction

end

end EulerNonuniqueness.Paper
