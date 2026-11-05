import EulerNonuniqueness.Section3.RelabeledDiskForcingAnalytic
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] relabeledAnalyticC1Group diskChartedEulerRealSpace

theorem diskRelabelMap_exists_uniform_lipschitz :
    ∃ radius > 0, ∃ constant : NNReal,
      (∀ angular : PeriodicC1HolderHalf, ‖angular‖ ≤ radius →
        ‖angular‖ < 1 / 2 ∧ ‖diskRelabelCurve angular 1‖ ≤ 3) ∧
      ∀ first second : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖second‖ ≤ radius →
        ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖ ≤ constant * ‖first - second‖ := by
  have analytic := diskRelabelMap_analyticAt (0 : PeriodicC1HolderHalf)
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ :=
    EulerNonuniqueness.General.lipschitzNear_of_analyticAt analytic
  have circle : diskRelabelCurve 0 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  have normSmall : ∀ᶠ angular : PeriodicC1HolderHalf in 𝓝 0, ‖diskRelabelCurve angular 1‖ < 3 := by
    apply analytic.continuousAt.norm (Iio_mem_nhds ?_)
    change ‖diskRelabelCurve 0 1‖ < 3
    rw [circle]
    linarith [standardCircleBanach_norm_bound]
  have angularSmall : ∀ᶠ angular : PeriodicC1HolderHalf in 𝓝 0, ‖angular‖ < 1 / 2 := by
    exact continuousAt_id.norm (Iio_mem_nhds (by norm_num))
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp
    (inter_mem nearby (inter_mem angularSmall normSmall))
  refine ⟨radius / 2, by positivity, constant, ?_, ?_⟩
  · intro angular bound
    have member := contained (show angular ∈ Metric.ball 0 radius by
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
    exact ⟨member.2.1, member.2.2.le⟩
  · intro first second firstBound secondBound
    have firstMember := contained (show first ∈ Metric.ball 0 radius by
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
    have secondMember := contained (show second ∈ Metric.ball 0 radius by
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
    exact lipschitz.norm_sub_le firstMember.1 secondMember.1

end EulerNonuniqueness.Paper
