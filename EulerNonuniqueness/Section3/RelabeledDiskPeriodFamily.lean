import EulerNonuniqueness.Section3.RelabeledDiskPeriod

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabeledFamilyHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance relabeledFamilyC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskRelabelCurve_real_smul (angular : PeriodicC1HolderHalf) (scalar : ℝ) :
    diskRelabelCurve (scalar • angular) 1 = diskRelabelCurve angular scalar := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [diskRelabelCurve_value, diskRelabelCurve_value]
  change Complex.exp ((1 : ℂ) * (Complex.I * (scalar • angular.val.1 label))) * standardCircle label = _
  simp only [Complex.real_smul, one_mul]
  congr 2
  ring

theorem relabeledDiskDerivative_eventually_exp_period (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    ∀ᶠ scalar in 𝓝 (0 : ℝ),
      EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
        (relabeledDiskDerivative (scalar • angular)) (4 * Real.pi) =
        ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  have angularConvergence : Tendsto (fun scalar : ℝ => ‖scalar • angular‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    have scaling : Continuous (fun scalar : ℝ => scalar • angular) :=
      ((ContinuousLinearMap.id ℝ ℝ).smulRight angular).continuous
    have normScaling : Continuous (fun scalar : ℝ => ‖scalar • angular‖) :=
      (continuous_norm : Continuous (fun value : PeriodicC1HolderHalf => ‖value‖)).comp scaling
    have actual := normScaling.tendsto (0 : ℝ)
    have zeroNorm : ‖(0 : PeriodicC1HolderHalf)‖ = (0 : ℝ) := by
      with_reducible
        exact norm_zero (E := PeriodicC1HolderHalf)
    simpa only [zero_smul, zeroNorm] using actual
  have shapeConvergence : Tendsto (fun scalar : ℝ => ‖diskRelabelCurve angular scalar - standardCircleBanach‖)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have actual := (diskRelabelCurve_analyticAt angular 0).continuousAt.tendsto.dist
      (tendsto_const_nhds (x := standardCircleBanach))
    have distance (value : PeriodicC1HolderHalf) : dist value standardCircleBanach = ‖value - standardCircleBanach‖ :=
      dist_eq_norm value standardCircleBanach
    simpa only [diskRelabelCurve_zero, dist_self, distance] using actual
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  filter_upwards [angularConvergence.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    shapeConvergence.eventually (eventually_lt_nhds threshold)] with scalar angularSmall shapeSmall
  have realScaled (label : ℝ) : star ((scalar • angular).val.1 label) = (scalar • angular).val.1 label := by
    change star (scalar • angular.val.1 label) = scalar • angular.val.1 label
    rw [star_smul, star_trivial, realValues]
  exact relabeledDiskDerivative_exp_period (scalar • angular) angularSmall realScaled
    (by simpa only [diskRelabelCurve_real_smul] using shapeSmall)

end

end EulerNonuniqueness.Paper
