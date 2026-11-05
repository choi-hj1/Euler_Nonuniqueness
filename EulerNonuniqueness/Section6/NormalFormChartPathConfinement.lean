import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem localNormalFormChart_exists_continuous_path_confinement
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ chartRadius > (0 : ℝ),
    ∀ (path : ℝ → ℝ × ℝ) (horizon : ℝ), ContinuousOn path (Icc 0 horizon) →
      |(path 0).1| + |(path 0).2| < radius →
      (∀ time ∈ Icc 0 horizon,
        |coordinate (path time).1| + |(path time).2 - graph (path time).1| ≤ chartRadius) →
      ∀ time ∈ Icc 0 horizon, |(path time).1| + |(path time).2| < radius := by
  obtain ⟨inverseRadius, inverseRadiusPositive, constant, constantOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  have constantPositive : 0 < constant := by linarith
  refine ⟨inverseRadius / 2, by positivity, inverseRadius / (4 * constant), by positivity, ?_⟩
  intro path horizon continuous initial small
  let monitor : ℝ → ℝ := fun time => |(path time).1| + |(path time).2| - inverseRadius / 2
  have monitorContinuous : ContinuousOn monitor (Icc 0 horizon) :=
    ((continuous_fst.comp_continuousOn continuous).abs.add
      (continuous_snd.comp_continuousOn continuous).abs).sub continuousOn_const
  have initialNegative : monitor 0 < 0 := by dsimp only [monitor]; linarith
  have negative := General.strictly_negative_of_strict_prefix_improvement monitorContinuous initialNegative
    (by
      intro time member closed _
      have pointSmall : |(path time).1| + |(path time).2| < inverseRadius := by
        have endpoint := closed time ⟨member.1, le_rfl⟩
        dsimp only [monitor] at endpoint
        linarith
      have bound := inverseBound (path time) 0 pointSmall (by simpa using inverseRadiusPositive)
      have chartBound : ‖localNormalFormChart graph coordinate (path time) -
          localNormalFormChart graph coordinate 0‖ ≤ inverseRadius / (4 * constant) := by
        have actual := small time member
        simp only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, coordinateZero, graphZero,
          sub_zero, Prod.mk_zero_zero, sub_zero, Prod.norm_def, Real.norm_eq_abs]
        exact (max_le (le_add_of_nonneg_right (abs_nonneg _))
          (le_add_of_nonneg_left (abs_nonneg _))).trans actual
      have scaled := bound.trans (mul_le_mul_of_nonneg_left chartBound constantPositive.le)
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at scaled
      have cancellation : constant * (inverseRadius / (4 * constant)) = inverseRadius / 4 := by
        field_simp
        ring
      rw [cancellation] at scaled
      dsimp only [monitor]
      linarith)
  intro time member
  have actual := negative time member
  dsimp only [monitor] at actual
  linarith

end EulerNonuniqueness.Section6
