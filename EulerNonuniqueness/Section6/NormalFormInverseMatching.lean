import EulerNonuniqueness.Section6.NormalFormChart

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormChart_exists_uniform_inverse_lipschitz
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      |first.1 - second.1| + |first.2 - second.2| ≤
        constant * ‖localNormalFormChart graph coordinate first - localNormalFormChart graph coordinate second‖ := by
  obtain ⟨inverse, inverseSmooth, inverseZero, leftInverse, _⟩ := localNormalFormChart_local_inverse
    graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have inverseOnce : ContDiffAt ℝ 1 inverse 0 := inverseSmooth.of_le (by norm_num)
  obtain ⟨inverseBound, region, regionMem, inverseLipschitz⟩ := inverseOnce.exists_lipschitzOnWith
  have regular := localNormalFormChart_regular graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have imageInside : ∀ᶠ point in 𝓝 (0 : ℝ × ℝ), localNormalFormChart graph coordinate point ∈ region :=
    (show Tendsto (localNormalFormChart graph coordinate) (𝓝 0) (𝓝 0) by
      simpa only [regular.2.1] using regular.1.continuousAt.tendsto).eventually regionMem
  obtain ⟨radius, radiusPositive, inside⟩ := Metric.mem_nhds_iff.mp (leftInverse.and imageInside)
  refine ⟨radius, radiusPositive, 2 * (inverseBound : ℝ) + 1, by have nonnegative := inverseBound.coe_nonneg; linarith, ?_⟩
  intro first second firstSmall secondSmall
  have pointInside (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) : point ∈ Metric.ball 0 radius := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le (le_add_of_nonneg_right (abs_nonneg point.2))
      (le_add_of_nonneg_left (abs_nonneg point.1))).trans_lt small
  have firstInside := inside (pointInside first firstSmall)
  have secondInside := inside (pointInside second secondSmall)
  have estimate := inverseLipschitz.dist_le_mul _ firstInside.2 _ secondInside.2
  rw [firstInside.1, secondInside.1, dist_eq_norm, dist_eq_norm] at estimate
  have firstComponent : |first.1 - second.1| ≤ ‖first - second‖ := by
    simpa only [Prod.fst_sub, Real.norm_eq_abs] using norm_fst_le (first - second)
  have secondComponent : |first.2 - second.2| ≤ ‖first - second‖ := by
    simpa only [Prod.snd_sub, Real.norm_eq_abs] using norm_snd_le (first - second)
  have nonnegative := norm_nonneg (localNormalFormChart graph coordinate first - localNormalFormChart graph coordinate second)
  nlinarith

end EulerNonuniqueness.Section6
