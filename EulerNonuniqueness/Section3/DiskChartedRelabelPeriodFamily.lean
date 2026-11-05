import EulerNonuniqueness.Section3.DiskChartedRelabelPeriod

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance chartedPeriodFamilyHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance chartedPeriodFamilyRealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskMaterialPerturbation_zero_real_smul (angular : PeriodicC1HolderHalf) (scalar : ℝ) :
    diskMaterialPerturbation 0 (scalar • angular) = scalar • diskMaterialPerturbation 0 angular := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * (0 + Complex.I * (scalar • angular.val.1 label)) =
    scalar • (standardCircle label * (0 + Complex.I * angular.val.1 label))
  simp only [zero_add, Complex.real_smul]
  ring

theorem diskChartedEulerField_relabel_eventually_exp_period
    (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    ∀ᶠ scalar in 𝓝 (0 : ℝ),
      EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
        (fderiv ℝ diskChartedEulerField (scalar • diskMaterialPerturbation 0 angular)) (4 * Real.pi) =
        ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  have neutralConvergence : Tendsto (fun scalar : ℝ => scalar • diskMaterialPerturbation 0 angular)
      (𝓝 0) (𝓝 (0 : PeriodicC1HolderHalf)) := by
    have actual := ((ContinuousLinearMap.id ℝ ℝ).smulRight (diskMaterialPerturbation 0 angular)).continuous.tendsto 0
    simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, zero_smul] using actual
  have shapeConvergence : Tendsto (fun scalar : ℝ => ‖diskRelabelCurve angular scalar - standardCircleBanach‖)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have actual := (diskRelabelCurve_analyticAt angular 0).continuousAt.tendsto.dist
      (tendsto_const_nhds (x := standardCircleBanach))
    have distance (value : PeriodicC1HolderHalf) : dist value standardCircleBanach = ‖value - standardCircleBanach‖ :=
      dist_eq_norm value standardCircleBanach
    simpa only [diskRelabelCurve_zero, dist_self, distance] using actual
  have threshold : (0 : ℝ) < min (1 / 3) (2 / (3 * Real.pi)) := by positivity
  filter_upwards [neutralConvergence.eventually diskStationaryChart_eventually_jacobian_equivalence,
    relabeledDiskDerivative_eventually_exp_period angular realValues,
    shapeConvergence.eventually (eventually_lt_nhds threshold)] with scalar jacobian period shapeSmall
  rw [← diskMaterialPerturbation_zero_real_smul] at jacobian
  obtain ⟨coordinates, chartDerivative, inverseIdentity, inverseActual⟩ := jacobian
  have realScaled (label : ℝ) : star ((scalar • angular).val.1 label) = (scalar • angular).val.1 label := by
    change star (scalar • angular.val.1 label) = scalar • angular.val.1 label
    rw [star_smul, star_trivial, realValues]
  have actual := diskChartedEulerField_relabel_exp_period (scalar • angular) realScaled
    (by simpa only [diskRelabelCurve_real_smul] using shapeSmall.trans_le (min_le_left _ _))
    (by simpa only [diskRelabelCurve_real_smul] using shapeSmall.trans_le (min_le_right _ _))
    coordinates chartDerivative inverseIdentity inverseActual period
  simpa only [diskMaterialPerturbation_zero_real_smul] using actual

end

end EulerNonuniqueness.Paper
