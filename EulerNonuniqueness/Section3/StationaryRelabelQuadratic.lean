import EulerNonuniqueness.Section3.DiskRotatingDerivative
import EulerNonuniqueness.Section3.ContourVelocityBoundedBilinear
import EulerNonuniqueness.General.StationaryQuadraticJetIdentity

namespace EulerNonuniqueness.Paper

open Filter
open scoped Topology

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryQuadHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance stationaryQuadC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance stationaryQuadOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance stationaryQuadOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem stationaryRelabel_actual_quadratic_jet_identity (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {radius : ℝ} (positive : 0 < radius) (small : radius < min 1 (2 / (3 * Real.pi))) :
    diskRotatingDerivative ((1 / 2 : ℝ) •
      diskRelabelGenerator angular (diskRelabelGenerator angular standardCircleBanach)) +
    contourVelocityBilinearCLM standardCircleBanach (innerRadius := 0) (outerRadius := radius)
      (by norm_num) positive small (by simp)
      (diskRelabelGenerator angular standardCircleBanach) (diskRelabelGenerator angular standardCircleBanach) = 0 := by
  let increment := fun parameter : ℝ => diskRelabelCurve angular parameter - standardCircleBanach
  let tangent := diskRelabelGenerator angular standardCircleBanach
  let curvature := (1 / 2 : ℝ) • diskRelabelGenerator angular tangent
  let quadratic : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    contourVelocityBilinearCLM standardCircleBanach (innerRadius := 0) (outerRadius := radius)
      (by norm_num) positive small (by simp)
  have firstSlope : Tendsto (fun parameter : ℝ => parameter⁻¹ • increment parameter)
      (𝓝[≠] (0 : ℝ)) (𝓝 tangent) := by
    dsimp only [increment, tangent, diskRelabelCurve]
    with_reducible
      exact EulerNonuniqueness.General.linearExponentialCurve_first_slope (Space := PeriodicC1HolderHalf)
        (diskRelabelGenerator angular) standardCircleBanach
  have secondSlope : Tendsto (fun parameter : ℝ => (parameter ^ 2)⁻¹ • (increment parameter - parameter • tangent))
      (𝓝[≠] (0 : ℝ)) (𝓝 curvature) := by
    dsimp only [increment, tangent, curvature, diskRelabelCurve]
    with_reducible
      exact EulerNonuniqueness.General.linearExponentialCurve_second_slope (Space := PeriodicC1HolderHalf)
        (diskRelabelGenerator angular) standardCircleBanach
  have normConvergence : Tendsto (fun parameter => ‖increment parameter‖) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have actual := (diskRelabelCurve_analyticAt angular 0).continuousAt.tendsto.dist
      (tendsto_const_nhds (x := standardCircleBanach))
    have distance (value : PeriodicC1HolderHalf) : dist value standardCircleBanach = ‖value - standardCircleBanach‖ :=
      dist_eq_norm value standardCircleBanach
    simpa only [diskRelabelCurve_zero, dist_self, distance] using actual
  have radiusLessOne : radius < 1 := small.trans_le (min_le_left _ _)
  have thresholdPositive : 0 < min (radius / 4) (min ((1 - radius) / 2) 1) :=
    lt_min (by positivity) (lt_min (by linarith) zero_lt_one)
  have tiny := normConvergence.eventually (eventually_lt_nhds thresholdPositive)
  have stationary := diskRelabelCurve_eventually_stationary angular realValues
  have circleStationary : extendedContourVelocity standardCircleBanach = (Complex.I / 2) • standardCircleBanach := by
    have atZero := stationary.self_of_nhds
    rw [diskRelabelCurve_zero] at atZero
    exact sub_eq_zero.mp atZero
  have stationaryRemainder : ∀ᶠ parameter in 𝓝[≠] (0 : ℝ),
      ‖diskRotatingDerivative (increment parameter) + quadratic (increment parameter) (increment parameter)‖ ≤
        contourVelocityAmbientCubicBound standardCircleBanach 0 radius * ‖increment parameter‖ ^ 3 := by
    filter_upwards [stationary.filter_mono nhdsWithin_le_nhds, tiny.filter_mono nhdsWithin_le_nhds]
      with parameter equilibrium tiny
    have firstSmall := (lt_min_iff.mp tiny).1.le
    have secondSmall := (lt_min_iff.mp (lt_min_iff.mp tiny).2).1.le
    have lastSmall := (lt_min_iff.mp (lt_min_iff.mp tiny).2).2.le
    have taylor := contourVelocity_cubic_taylor_bound standardCircleBanach (increment parameter)
      (innerRadius := 0) (outerRadius := radius) (by norm_num) positive small (by simp)
      (by simpa only [sub_zero] using firstSmall) secondSmall lastSmall
    rw [← contourVelocityBilinearCLM_diagonal standardCircleBanach (increment parameter)
      (innerRadius := 0) (outerRadius := radius) (by norm_num) positive small (by simp)] at taylor
    have actualVelocity : extendedContourVelocity (diskRelabelCurve angular parameter) =
        (Complex.I / 2) • diskRelabelCurve angular parameter := sub_eq_zero.mp equilibrium
    have reconstruction : standardCircleBanach + increment parameter = diskRelabelCurve angular parameter := by
      dsimp only [increment]
      abel
    have expressionIdentity : extendedContourVelocity (standardCircleBanach + increment parameter) -
        extendedContourVelocity standardCircleBanach -
        fderiv ℝ extendedContourVelocity standardCircleBanach (increment parameter) -
        quadratic (increment parameter) (increment parameter) =
      -(diskRotatingDerivative (increment parameter) + quadratic (increment parameter) (increment parameter)) := by
      rw [reconstruction, actualVelocity, circleStationary, diskRotatingDerivative_apply]
      dsimp only [increment]
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change (Complex.I / 2) * _ - (Complex.I / 2) * _ - _ - _ =
        -(_ - (Complex.I / 2) * (_ - _) + _)
      ring <;> rfl
    change ‖extendedContourVelocity (standardCircleBanach + increment parameter) -
      extendedContourVelocity standardCircleBanach -
      fderiv ℝ extendedContourVelocity standardCircleBanach (increment parameter) -
      quadratic (increment parameter) (increment parameter)‖ ≤ _ at taylor
    rw [expressionIdentity] at taylor
    have negNorm (value : PeriodicC1HolderHalf) : ‖-value‖ = ‖value‖ := norm_neg value
    rw [negNorm] at taylor
    exact taylor
  with_reducible
    exact EulerNonuniqueness.General.stationary_quadratic_second_jet_identity (Space := PeriodicC1HolderHalf)
      diskRotatingDerivative quadratic increment tangent curvature
      (contourVelocityAmbientCubicBound standardCircleBanach 0 radius)
      (diskRotatingDerivative_relabel_tangent_zero angular realValues) firstSlope secondSlope stationaryRemainder

theorem stationaryRelabel_actual_quadratic_coefficient (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {radius : ℝ} (positive : 0 < radius) (small : radius < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBilinearCLM standardCircleBanach (innerRadius := 0) (outerRadius := radius)
      (by norm_num) positive small (by simp)
      (diskRelabelGenerator angular standardCircleBanach) (diskRelabelGenerator angular standardCircleBanach) =
      (1 / 2 : ℝ) • diskRotatingDerivative (c1Product standardCircleBanach (c1Product angular angular)) := by
  have jet := stationaryRelabel_actual_quadratic_jet_identity angular realValues positive small
  have derivativeEquality : diskRelabelGenerator angular (diskRelabelGenerator angular standardCircleBanach) =
      -c1Product standardCircleBanach (c1Product angular angular) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (Complex.I * angular.val.1 label) * ((Complex.I * angular.val.1 label) * standardCircle label) =
      -(standardCircle label * (angular.val.1 label * angular.val.1 label))
    linear_combination (standardCircle label * angular.val.1 label ^ 2) * Complex.I_sq
  rw [derivativeEquality, map_smul] at jet
  have negative : diskRotatingDerivative (-c1Product standardCircleBanach (c1Product angular angular)) =
      -(diskRotatingDerivative (c1Product standardCircleBanach (c1Product angular angular))) := by
    have inputNegative (value : PeriodicC1HolderHalf) : -value = (-1 : ℝ) • value := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change -value.val.1 label = (-1 : ℝ) • value.val.1 label
      simp only [neg_one_smul]
    rw [inputNegative, map_smul]
    exact (inputNegative _).symm
  rw [negative] at jet
  have scalarNegative (value : PeriodicC1HolderHalf) : (1 / 2 : ℝ) • -value = -((1 / 2 : ℝ) • value) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (1 / 2 : ℝ) • -value.val.1 label = -((1 / 2 : ℝ) • value.val.1 label)
    exact smul_neg _ _
  rw [scalarNegative] at jet
  apply eq_of_sub_eq_zero
  convert jet using 1 <;> abel

end

end EulerNonuniqueness.Paper
