import EulerNonuniqueness.Section5.CascadeMaterialForeignGeometry
import EulerNonuniqueness.Section5.CascadeExtentScalarBudget
import EulerNonuniqueness.Section6.MovingBlockDeformationSpeed

noncomputable section

open Set Metric
open scoped BigOperators

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem blockExtentVelocity_bound_of_monitors {count : ℕ}
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
    (material : ∀ patch label,
      (trajectory.movingFamily.patch patch).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales trajectory.movingFamily.patchMotion time)
          ((trajectory.movingFamily.patch patch).boundary time label))
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source
      (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (extent : ∀ label, cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (lower : ∀ receiver source, cascadeAnchorLowerMonitor scales receiver source
      (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.location (index.val + 1) / 1000)
    (control : ∀ index patch, BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch (1 / 16))
    (index : Fin count) :
    ‖trajectory.blockExtentVelocity index time‖ ≤
      ((4 / Real.pi) * (24 / factor) ^ 2 * scales.strain) * ‖trajectory.blockExtentVector index time‖ +
        (10 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor +
          (512 / Real.pi) * (24 / factor) ^ 3 * scales.radius (index.val + 1) ^ 2 * scales.hessian) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have radiusNonnegative : 0 ≤ scales.radius (index.val + 1) := Real.sqrt_nonneg _
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro target
  rw [trajectory.blockExtentVelocity_eq_centroid_offset_deriv initialCircles pathInside]
  have gapPositive : 0 < factor * scales.length (index.val + 1) := mul_pos factorPositive lengthPositive
  have internalGap (target source : Fin 4) (different : source ≠ target) :
      factor * scales.length (index.val + 1) ≤
        ‖patchCentroid trajectory.movingFamily.patchMotion time index target -
          patchCentroid trajectory.movingFamily.patchMotion time index source‖ := by
    have estimate := internal (index, target) (index, source)
    rw [cascadeInternalGapMonitor, if_pos (show (index, target).1 = (index, source).1 ∧
      (index, target).2 ≠ (index, source).2 from ⟨rfl, different.symm⟩)] at estimate
    rw [trajectory.cascadeCenters_eq_patchCentroid initialCircles pathInside,
      trajectory.cascadeCenters_eq_patchCentroid initialCircles pathInside] at estimate
    exact sub_nonpos.mp estimate
  have foreign (source : Fin count) (member : source ∈ Finset.univ.erase index) :=
    trajectory.cascade_foreign_geometry_of_monitors scales radii initialCircles pathInside
      factorPositive factorSmall extent lower radiusLocation index source (Finset.mem_erase.mp member).1
  have actual := trajectory.movingFamily.patchCentroid_relative_velocity_bound_of_boundary_control
    evolution inside amplitudePositive frequencyPositive ratioPositive index (fun _ => pathInside)
    (fun patch => material (finProdFinEquiv (index, patch))) gapPositive (control index)
    (by norm_num) le_rfl (by linarith [radiusInternal index]) internalGap
    (fun patch => by
      rw [← trajectory.blockExtentVector_eq_centroid_offset initialCircles pathInside]
      exact norm_le_pi_norm _ patch)
    (cascadeForeignDistance scales factor index) (fun source member => (foreign source member).1)
    (fun source _ patch => trajectory.domain_subset_centroid_ball scales radii initialCircles pathInside source patch)
    (fun source member => (foreign source member).2.1)
    (fun source member => (foreign source member).2.2.1)
    (fun patch source member => (foreign source member).2.2.2.1 patch)
    (fun patch source member => (foreign source member).2.2.2.2.1 patch)
    (fun source member => (foreign source member).2.2.2.2.2) target
  have internalEstimate := cascade_internal_deformation_speed_le omegaPositive lengthPositive radiusNonnegative
    factorPositive (radiusInternal index)
  rw [← Scales.circulation] at internalEstimate
  have third := scales.sum_cascadeForeignMoment_le frequencyBound ratioBound alphaPositive factorPositive index 3
  change _ ≤ (24 / factor) ^ 3 * scales.hessian at third
  have strainEstimate := scales.cascadeForeignStrain_le frequencyBound ratioBound alphaPositive factorPositive index
  have thirdWeighted := mul_le_mul_of_nonneg_left third
    (by positivity : 0 ≤ 4096 * scales.radius (index.val + 1) ^ 2 * (1 / 16) / Real.pi)
  have strainWeighted := mul_le_mul_of_nonneg_right strainEstimate (norm_nonneg (trajectory.blockExtentVector index time))
  have mainIdentity : 4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| /
      (factor * scales.length (index.val + 1)) =
        4 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor := by
    rw [abs_of_pos (by positivity)]
    field_simp [lengthPositive.ne', factorPositive.ne']
    <;> ring
  rw [mainIdentity] at actual
  have sums := add_le_add (add_le_add
    (add_le_add_left internalEstimate
      (4 * scales.omega (index.val + 1) * scales.length (index.val + 1) / factor))
    thirdWeighted) strainWeighted
  exact (actual.trans (mul_le_mul_of_nonneg_left sums (by norm_num))).trans_eq (by ring)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
