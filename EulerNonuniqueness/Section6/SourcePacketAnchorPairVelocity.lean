import EulerNonuniqueness.Section5.CascadeCenterDriftBound
import EulerNonuniqueness.Section5.CascadeExteriorAnchorDifference
import EulerNonuniqueness.General.FourAverageNorm

noncomputable section

open Set Metric
open scoped BigOperators

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem source_packet_anchor_pair_velocity_small {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius cutoffGap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius cutoffGap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (radii : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {horizon time : ℝ} (evolution : FinitePatchEvolution scales trajectory.movingFamily.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (pathInside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (material : ∀ patch label, (trajectory.movingFamily.patch patch).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales trajectory.movingFamily.patchMotion time)
        ((trajectory.movingFamily.patch patch).boundary time label))
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source
      (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (extent : ∀ label, cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (lower : ∀ receiver source, cascadeAnchorLowerMonitor scales receiver source (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (upper : ∀ receiver source, cascadeAnchorUpperMonitor scales receiver source (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.location (index.val + 1) / 1000)
    (control : ∀ index patch, BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch (1 / 16))
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (forcingBudget : ∀ index : Fin count,
      10 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
        (512 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian ≤ tolerance * scales.location (index.val + 1) / 1000)
    (strainBudget : (2 / Real.pi) * (24 / factor) ^ 2 * scales.strain ≤ tolerance / 64)
    (crossBudget : (144 / (Real.pi * factor)) * scales.strain ≤ tolerance / 32)
    (first second : Fin count) (different : first ≠ second) :
    ‖(∑ patch : Fin 4, (trajectory.velocity time).2.1 (finProdFinEquiv (first, patch))) / 4 -
      (∑ patch : Fin 4, (trajectory.velocity time).2.1 (finProdFinEquiv (second, patch))) / 4‖ ≤
      tolerance * |scales.location (first.val + 1) - scales.location (second.val + 1)| / 8 := by
  let anchors := fun index => quadrupoleCenter trajectory.movingFamily.patchMotion time index
  let velocities := fun index : Fin count =>
    (∑ patch : Fin 4, (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) / 4
  let fields := fun index => biotSavart (externalPatchVorticity scales trajectory.movingFamily.patchMotion time index) (anchors index)
  have drift (index : Fin count) : ‖velocities index - fields index‖ ≤ tolerance * scales.location (index.val + 1) / 1000 := by
    have average := EulerNonuniqueness.General.norm_four_average_sub_le
      (fun patch => (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) (fields index)
      (fun patch => trajectory.centerVelocity_anchor_drift_bound_of_monitors scales radii initialCircles evolution inside
        pathInside amplitudePositive frequencyBound ratioBound alphaPositive material factorPositive factorSmall internal extent
        lower radiusInternal radiusLocation control index patch)
    have extentNorm : ‖trajectory.blockExtentVector index time‖ ≤ scales.location (index.val + 1) / 100 := by
      apply (pi_norm_le_iff_of_nonneg (div_nonneg (scales.location_pos _).le (by norm_num))).mpr
      intro patch
      exact sub_nonpos.mp (extent (index, patch))
    have twice : 2 * (5 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
        (256 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian) =
        10 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
        (512 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian := by ring
    have halfBudget := forcingBudget index
    rw [← twice] at halfBudget
    have halfBound : 5 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
        (256 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian ≤
          tolerance * scales.location (index.val + 1) / 2000 := by linarith
    have weighted := mul_le_mul strainBudget extentNorm (norm_nonneg _) (by positivity : (0 : ℝ) ≤ tolerance / 64)
    exact average.trans ((add_le_add halfBound weighted).trans (by nlinarith [scales.location_pos (index.val + 1)]))
  have pairBound := upper first second
  rw [cascadeAnchorUpperMonitor, if_neg different,
    trajectory.cascadeBlockCenter_eq_quadrupoleCenter initialCircles pathInside,
    trajectory.cascadeBlockCenter_eq_quadrupoleCenter initialCircles pathInside] at pairBound
  have external := trajectory.exteriorBlockAnchorDifference_bound scales radii initialCircles evolution inside pathInside
    amplitudePositive frequencyBound ratioBound alphaPositive factorPositive factorSmall extent lower radiusLocation first second different
  have commonWeighted := mul_le_mul strainBudget (sub_nonpos.mp pairBound) (norm_nonneg _) (by positivity : (0 : ℝ) ≤ tolerance / 64)
  have crossWeighted := mul_le_mul_of_nonneg_right crossBudget
    (abs_nonneg (scales.location (first.val + 1) - scales.location (second.val + 1)))
  have fieldDifference : ‖fields first - fields second‖ ≤
      tolerance * |scales.location (first.val + 1) - scales.location (second.val + 1)| / 16 :=
    external.trans ((add_le_add commonWeighted crossWeighted).trans_eq (by ring))
  have triangle := norm_sub_le_norm_sub_add_norm_sub (velocities first) (fields first) (velocities second)
  have last := norm_sub_le_norm_sub_add_norm_sub (fields first) (fields second) (velocities second)
  rw [norm_sub_rev (fields second) (velocities second)] at last
  have locations := scales.location_sum_le_three_distance
    (show first.val + 1 ≠ second.val + 1 from fun equal => different (Fin.ext (Nat.add_right_cancel equal)))
  have scaledLocations := mul_le_mul_of_nonneg_left locations tolerancePositive.le
  have scaledLinear : tolerance * scales.location (first.val + 1) + tolerance * scales.location (second.val + 1) ≤
      3 * (tolerance * |scales.location (first.val + 1) - scales.location (second.val + 1)|) := by
    convert scaledLocations using 1 <;> ring
  have nonnegative := mul_nonneg tolerancePositive.le
    (abs_nonneg (scales.location (first.val + 1) - scales.location (second.val + 1)))
  change ‖velocities first - velocities second‖ ≤ _
  linarith [drift first, drift second, abs_nonneg (scales.location (first.val + 1) - scales.location (second.val + 1))]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

