import EulerNonuniqueness.Section3.DiskStationaryJacobian
import EulerNonuniqueness.Section3.DiskStationaryArea
import EulerNonuniqueness.Section3.RelabeledDiskPeriodFamily
import EulerNonuniqueness.General.EquilibriumChartPeriod

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance chartedRelabelPeriodHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance chartedRelabelPeriodRealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance chartedRelabelPeriodOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedRelabelPeriodOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedRelabelPeriodUniformGroup : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)

theorem diskEulerRotatingField_hasFDerivAt_relabel (angular : PeriodicC1HolderHalf)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt diskEulerRotatingField (relabeledDiskDerivative angular) (diskRelabelCurve angular 1) := by
  have actual : HasFDerivAt extendedContourVelocity
      (fderiv ℝ extendedContourVelocity (diskRelabelCurve angular 1)) (diskRelabelCurve angular 1) :=
    DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (differentiableAt_extendedContourVelocity (diskRelabelCurve angular 1) small)
  have rotation : HasFDerivAt (c1Product (c1Constant (Complex.I / 2)))
      (c1ProductCLM (c1Constant (Complex.I / 2))) (diskRelabelCurve angular 1) := by
    change HasFDerivAt (c1ProductCLM (c1Constant (Complex.I / 2)))
      (c1ProductCLM (c1Constant (Complex.I / 2))) (diskRelabelCurve angular 1)
    with_reducible
      exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf) (c1ProductCLM (c1Constant (Complex.I / 2)))
  exact HasFDerivAt.sub (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) actual rotation

theorem diskEulerRotatingField_relabel_zero (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3)
    (chordSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 2 / (3 * Real.pi)) :
    diskEulerRotatingField (diskRelabelCurve angular 1) = 0 := by
  unfold diskEulerRotatingField
  rw [extendedContourVelocity_parameterized_unit_disk (diskRelabelCurve angular 1) small chordSmall
    (diskRelabelCurve_unit_norm angular realValues 1)]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change Complex.I / 2 * (diskRelabelCurve angular 1).val.1 label -
    Complex.I / 2 * (diskRelabelCurve angular 1).val.1 label = 0
  ring

theorem diskChartedEulerField_relabel_exp_period
    (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3)
    (chordSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 2 / (3 * Real.pi))
    (coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf)
    (chartDerivative : HasFDerivAt diskStationaryChart coordinates.toContinuousLinearMap
      (diskMaterialPerturbation 0 angular))
    (inverseIdentity : diskChartInverseDerivative (diskMaterialPerturbation 0 angular) =
      coordinates.symm.toContinuousLinearMap)
    (inverseActual : HasFDerivAt diskChartInverseDerivative
      (fderiv ℝ diskChartInverseDerivative (diskMaterialPerturbation 0 angular))
      (diskMaterialPerturbation 0 angular))
    (period : EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
      (relabeledDiskDerivative angular) (4 * Real.pi) = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
      (fderiv ℝ diskChartedEulerField (diskMaterialPerturbation 0 angular)) (4 * Real.pi) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  have near : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    lt_min (small.trans (by norm_num)) chordSmall
  have fieldDerivative := diskEulerRotatingField_hasFDerivAt_relabel angular near
  have equilibrium := diskEulerRotatingField_relabel_zero angular realValues small chordSmall
  rw [← diskStationaryChart_relabel angular realValues] at fieldDerivative equilibrium
  let inverseLinear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskChartInverseDerivative (diskMaterialPerturbation 0 angular)
  unfold diskChartedEulerField
  with_reducible
    exact EulerNonuniqueness.General.equilibrium_chart_derivative_exp_period
      (Space := PeriodicC1HolderHalf) diskEulerRotatingField diskStationaryChart diskChartInverseDerivative
      (diskMaterialPerturbation 0 angular) (relabeledDiskDerivative angular) coordinates inverseLinear
      fieldDerivative chartDerivative inverseActual inverseIdentity equilibrium period

end

end EulerNonuniqueness.Paper
