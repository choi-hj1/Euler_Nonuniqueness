import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.Section6.NormalFormOrbitCompatibility

noncomputable section

open Set
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormError_contDiffAt_one {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (frequency : ℝ) : ContDiffAt ℝ 1 (localNormalFormError frequency graph coordinate) 0 := by
  have graphPartial : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => deriv graph point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := deriv graph) 0 (scalar_deriv_contDiffAt_one graphSmooth) contDiffAt_fst
  have coordinatePartial : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => deriv coordinate point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := deriv coordinate) 0 (scalar_deriv_contDiffAt_one coordinateSmooth) contDiffAt_fst
  have graphValue : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => graph point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := graph) 0 (graphSmooth.of_le (by norm_num)) contDiffAt_fst
  have coordinateValue : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => coordinate point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := coordinate) 0 (coordinateSmooth.of_le (by norm_num)) contDiffAt_fst
  have field : ContDiffAt ℝ 1 (shapeChartVelocity frequency) 0 :=
    (shapeChartVelocity_contDiffAt frequency).of_le (by norm_num)
  exact (coordinatePartial.mul field.fst |>.sub (coordinateValue.const_smul (2 * Real.sqrt 2 * frequency))).prodMk
    ((field.snd.sub (graphPartial.mul field.fst)).add
      ((contDiffAt_snd.sub graphValue).const_smul (2 * Real.sqrt 2 * frequency)))

theorem localNormalFormError_exists_uniform_linear_chart_bound
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ point : ℝ × ℝ,
      |point.1| + |point.2| < radius →
      ‖localNormalFormError 1 graph coordinate point‖ ≤
        constant * (|coordinate point.1| + |point.2 - graph point.1|) := by
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨bound, region, regionMem, lipschitz⟩ :=
    (localNormalFormError_contDiffAt_one graphSmooth coordinateSmooth 1).exists_lipschitzOnWith
  obtain ⟨errorRadius, errorPositive, errorInside⟩ := Metric.mem_nhds_iff.mp regionMem
  refine ⟨min inverseRadius errorRadius, lt_min inversePositive errorPositive,
    (bound : ℝ) * inverseConstant + 1, by have nonnegative := bound.coe_nonneg; nlinarith, ?_⟩
  intro point small
  have normBound : ‖point‖ ≤ |point.1| + |point.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have inside : point ∈ region := errorInside (by
    rw [Metric.mem_ball, dist_zero_right]
    exact normBound.trans_lt (small.trans_le (min_le_right _ _)))
  have zeroInside : (0 : ℝ × ℝ) ∈ region := mem_of_mem_nhds regionMem
  have estimate := lipschitz.dist_le_mul point inside 0 zeroInside
  rw [localNormalFormError_at_zero graphZero coordinateZero, dist_zero_right, dist_zero_right] at estimate
  have inverse := inverseBound point 0 (small.trans_le (min_le_left _ _)) (by simpa using inversePositive)
  have chartZero : localNormalFormChart graph coordinate 0 = 0 := by
    simp only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, graphZero, coordinateZero, sub_zero, Prod.mk_zero_zero]
  rw [chartZero, sub_zero] at inverse
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at inverse
  have chartNorm : ‖localNormalFormChart graph coordinate point‖ ≤ |coordinate point.1| + |point.2 - graph point.1| := by
    change max |coordinate point.1| |point.2 - graph point.1| ≤ _
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have rawBound := inverse.trans (mul_le_mul_of_nonneg_left chartNorm (by linarith))
  have actual := estimate.trans (mul_le_mul_of_nonneg_left (normBound.trans rawBound) bound.coe_nonneg)
  nlinarith [abs_nonneg (coordinate point.1), abs_nonneg (point.2 - graph point.1)]

end EulerNonuniqueness.Section6
