import EulerNonuniqueness.Section6.NormalFormChart

noncomputable section

open Set
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormChart_exists_uniform_forward_bound
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ point : ℝ × ℝ,
      |point.1| + |point.2| < radius →
      |coordinate point.1| + |point.2 - graph point.1| ≤ constant * (|point.1| + |point.2|) := by
  have regular := localNormalFormChart_regular graphSmooth coordinateSmooth graphZero coordinateZero
    graphDerivative coordinateDerivative
  obtain ⟨bound, region, regionMem, lipschitz⟩ :=
    (regular.1.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).exists_lipschitzOnWith
  obtain ⟨radius, radiusPositive, inside⟩ := Metric.mem_nhds_iff.mp regionMem
  refine ⟨radius, radiusPositive, 2 * (bound : ℝ) + 1, by have positive := bound.coe_nonneg; linarith, ?_⟩
  intro point small
  have pointInside : point ∈ region := inside (by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))).trans_lt small)
  have zeroInside : (0 : ℝ × ℝ) ∈ region := mem_of_mem_nhds regionMem
  have estimate := lipschitz.dist_le_mul point pointInside 0 zeroInside
  rw [regular.2.1, dist_zero_right, dist_zero_right] at estimate
  have first := norm_fst_le (localNormalFormChart graph coordinate point)
  have second := norm_snd_le (localNormalFormChart graph coordinate point)
  have pointBound : ‖point‖ ≤ |point.1| + |point.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have actual := estimate.trans (mul_le_mul_of_nonneg_left pointBound bound.coe_nonneg)
  change ‖coordinate point.1‖ ≤ _ at first
  change ‖point.2 - graph point.1‖ ≤ _ at second
  rw [Real.norm_eq_abs] at first second
  nlinarith [abs_nonneg point.1, abs_nonneg point.2]

end EulerNonuniqueness.Section6
