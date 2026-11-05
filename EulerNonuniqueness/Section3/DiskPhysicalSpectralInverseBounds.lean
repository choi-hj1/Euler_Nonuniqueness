import EulerNonuniqueness.Section3.DiskPhysicalSpectralFirstOrderBounds

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralInverseBoundsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd

theorem diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
        HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative data) data ∧
          ‖diskPhysicalSpectralInverseDerivative data‖ ≤ constant) ∧
      (∀ first second : PeriodicC1HolderHalf,
        ‖first - standardCircleBanach‖ ≤ radius → ‖second - standardCircleBanach‖ ≤ radius →
        ‖diskPhysicalSpectralCoordinate first - diskPhysicalSpectralCoordinate second‖ ≤ constant * ‖first - second‖) ∧
      ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
        ‖diskPhysicalSpectralCoordinate data‖ ≤ constant * ‖data - standardCircleBanach‖ := by
  obtain ⟨chartRadius, chartPositive, constant, constantOne, chartBounds, _⟩ :=
    diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds
  have coordinateSmall : ∀ᶠ data in 𝓝 standardCircleBanach, ‖diskPhysicalSpectralCoordinate data‖ < chartRadius := by
    have limit : Tendsto diskPhysicalSpectralCoordinate (𝓝 standardCircleBanach) (𝓝 (0 : PeriodicC1HolderHalf)) := by
      simpa only [diskPhysicalSpectralCoordinate_circle] using diskPhysicalSpectralCoordinate_continuousAt_circle.tendsto
    simpa only [Metric.mem_ball, dist_zero_right] using limit.eventually (Metric.ball_mem_nhds _ chartPositive)
  have valid : ∀ᶠ data in 𝓝 standardCircleBanach,
      HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative data) data ∧
        ‖diskPhysicalSpectralInverseDerivative data‖ ≤ constant := by
    filter_upwards [diskPhysicalSpectralCoordinate_eventually_inverse_derivative, coordinateSmall]
      with data inverse small
    refine ⟨inverse.2.1, ?_⟩
    have bound := (chartBounds (diskPhysicalSpectralCoordinate data) small.le).2
    change ‖diskPhysicalSpectralInverseDerivative
      (diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate data)))‖ ≤ constant at bound
    rwa [inverse.1] at bound
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp valid
  let radius := outerRadius / 2
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have localBounds (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ ≤ radius) :
      HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative data) data ∧
        ‖diskPhysicalSpectralInverseDerivative data‖ ≤ constant := by
    apply contained
    rw [dist_eq_norm]
    exact small.trans_lt (by dsimp [radius]; linarith)
  have difference (first second : PeriodicC1HolderHalf)
      (firstSmall : ‖first - standardCircleBanach‖ ≤ radius)
      (secondSmall : ‖second - standardCircleBanach‖ ≤ radius) :
      ‖diskPhysicalSpectralCoordinate first - diskPhysicalSpectralCoordinate second‖ ≤ constant * ‖first - second‖ := by
    have derivative (data : PeriodicC1HolderHalf) (member : data ∈ closedBall standardCircleBanach radius) :=
      localBounds data (by simpa only [Metric.mem_closedBall, dist_eq_norm] using member)
    have estimate := (convex_closedBall standardCircleBanach radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun data member => (derivative data member).1.hasFDerivWithinAt)
      (fun data member => (derivative data member).2)
      (show second ∈ closedBall standardCircleBanach radius by simpa only [Metric.mem_closedBall, dist_eq_norm] using secondSmall)
      (show first ∈ closedBall standardCircleBanach radius by simpa only [Metric.mem_closedBall, dist_eq_norm] using firstSmall)
    exact estimate
  refine ⟨radius, radiusPositive, constant, constantOne, localBounds, difference, ?_⟩
  intro data small
  have bound := difference data standardCircleBanach small (by simpa using radiusPositive.le)
  simpa only [diskPhysicalSpectralCoordinate_circle, sub_zero] using bound

theorem diskPhysicalSpectralCoordinate_lipschitzNear_circle :
    EulerNonuniqueness.General.LipschitzNear diskPhysicalSpectralCoordinate standardCircleBanach := by
  obtain ⟨radius, positive, constant, one, _, difference, _⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds
  refine ⟨⟨constant, by linarith⟩, closedBall standardCircleBanach radius, closedBall_mem_nhds _ positive, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro first firstMember second secondMember
  simpa only [dist_eq_norm] using difference first second
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using firstMember)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using secondMember)

end EulerNonuniqueness.Paper
