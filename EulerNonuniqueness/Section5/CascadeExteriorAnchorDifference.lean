import EulerNonuniqueness.Section5.CascadeMaterialForeignGeometry
import EulerNonuniqueness.Section5.CascadeCommonStrainBound
import EulerNonuniqueness.Section6.MovingExteriorPairDifference

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem exteriorBlockAnchorDifference_bound {count : ℕ}
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
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (extent : ∀ label, cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (lower : ∀ receiver source, cascadeAnchorLowerMonitor scales receiver source
      (trajectory.movingFamily.cascadeCenters time) ≤ 0)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.location (index.val + 1) / 1000)
    (first second : Fin count) (different : first ≠ second) :
    ‖biotSavart (externalPatchVorticity scales trajectory.movingFamily.patchMotion time first)
        (quadrupoleCenter trajectory.movingFamily.patchMotion time first) -
      biotSavart (externalPatchVorticity scales trajectory.movingFamily.patchMotion time second)
        (quadrupoleCenter trajectory.movingFamily.patchMotion time second)‖ ≤
      ((2 / Real.pi) * (24 / factor) ^ 2 * scales.strain) *
        ‖quadrupoleCenter trajectory.movingFamily.patchMotion time first -
          quadrupoleCenter trajectory.movingFamily.patchMotion time second‖ +
      (144 / (Real.pi * factor)) * scales.strain *
        |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have geometry (receiver source : Fin count) (ne : source ≠ receiver) :=
    trajectory.cascade_foreign_geometry_of_monitors scales radii initialCircles pathInside
      factorPositive factorSmall extent lower radiusLocation receiver source ne
  have actual := evolution.externalPatch_biotSavart_receiver_difference_bound inside
    amplitudePositive frequencyPositive ratioPositive first second different
    (fun source => factor * scales.location (source.val + 1) / 24) (geometry first second different.symm).1
    (fun source _ => by have positive := scales.location_pos (source.val + 1); positivity)
    (fun source member patch position inDomain =>
      (cascadeForeignDistance_ge_source scales factorPositive first source
        (Finset.mem_erase.mp (Finset.mem_erase.mp member).2).1.symm).trans
          ((geometry first source (Finset.mem_erase.mp (Finset.mem_erase.mp member).2).1).2.2.2.2.2 patch position inDomain))
    (fun source member patch position inDomain =>
      (cascadeForeignDistance_ge_source scales factorPositive second source
        (Finset.mem_erase.mp member).1.symm).trans
          ((geometry second source (Finset.mem_erase.mp member).1).2.2.2.2.2 patch position inDomain))
    ((geometry first second different.symm).2.2.2.2.2)
    (fun patch position member => by
      rw [cascadeForeignDistance_symm scales factor first second]
      exact (geometry second first different).2.2.2.2.2 patch position member)
  have common := mul_le_mul_of_nonneg_right
    (scales.sum_cascadeCommonStrain_le frequencyBound ratioBound alphaPositive factorPositive first second)
    (norm_nonneg (quadrupoleCenter trajectory.movingFamily.patchMotion time first -
      quadrupoleCenter trajectory.movingFamily.patchMotion time second))
  have cross := scales.cascade_cross_source_velocity_le frequencyBound ratioBound alphaPositive factorPositive first second different
  have total := add_le_add common cross
  exact actual.trans (by simpa only [add_assoc] using total)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
