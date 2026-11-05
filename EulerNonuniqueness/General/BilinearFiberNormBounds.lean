import EulerNonuniqueness.General.LocalFiberOperatorBounds

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_half_bilinear_le (bilinear second : BilinearEnd Space)
    (factor : ∀ first right, bilinear first right = (1 / 2 : ℝ) • second first right) :
    ‖bilinear‖ ≤ (1 / 2 : ℝ) * ‖second‖ := by
  apply ContinuousLinearMap.opNorm_le_bound bilinear (by positivity)
  intro first
  apply ContinuousLinearMap.opNorm_le_bound (bilinear first) (by positivity)
  intro right
  rw [factor, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖second first‖ * ‖right‖) := by
      gcongr
      exact (second first).le_opNorm _
    _ ≤ (1 / 2 : ℝ) * ((‖second‖ * ‖first‖) * ‖right‖) := by
      gcongr
      exact second.le_opNorm _
    _ = _ := by ring

theorem norm_bilinear_fiber_conjugate_le (inverse coordinates : Space →L[ℝ] Space)
    (bilinear : BilinearEnd Space) :
    ‖bilinearPostcompose inverse (bilinear.bilinearComp coordinates coordinates)‖ ≤
      ‖inverse‖ * ‖bilinear‖ * ‖coordinates‖ ^ 2 := by
  apply (norm_bilinearPostcompose_le _ _).trans
  calc
    _ ≤ ‖inverse‖ * (‖bilinear‖ * ‖coordinates‖ * ‖coordinates‖) :=
      mul_le_mul_of_nonneg_left (norm_bilinearComp_le _ _ _) (norm_nonneg _)
    _ = _ := by ring

theorem exists_eventually_bilinear_fiber_conjugate_bound
    (projection : Space →L[ℝ] Space) (coordinates inverse : Space → Space →L[ℝ] Space)
    (quadratic second : Space → BilinearEnd Space)
    (coordinatesContinuous : ContinuousAt coordinates (0 : Space))
    (inverseContinuous : ContinuousAt inverse (0 : Space))
    (secondContinuous : ContinuousAt second (0 : Space))
    (factor : ∀ base first right, quadratic base first right = (1 / 2 : ℝ) • second base first right) :
    ∃ bound ≥ 0, ∀ᶠ value in 𝓝 (0 : Space),
      ‖bilinearPostcompose (inverse value)
        ((quadratic (projection value)).bilinearComp (coordinates value) (coordinates value))‖ ≤ bound := by
  obtain ⟨coordinateBound, coordinateNonnegative, coordinateEstimate⟩ :=
    exists_eventually_norm_bound coordinatesContinuous
  obtain ⟨inverseBound, inverseNonnegative, inverseEstimate⟩ :=
    exists_eventually_norm_bound inverseContinuous
  obtain ⟨secondBound, secondNonnegative, secondEstimate⟩ :=
    exists_eventually_norm_bound (Space := Space) (Target := BilinearEnd Space) secondContinuous
  have limit : Tendsto projection (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using projection.continuous.tendsto (0 : Space)
  refine ⟨inverseBound * ((1 / 2 : ℝ) * secondBound) * coordinateBound ^ 2, by positivity, ?_⟩
  filter_upwards [coordinateEstimate, inverseEstimate, limit.eventually secondEstimate]
    with value coordinateSmall inverseSmall secondSmall
  have quadraticSmall : ‖quadratic (projection value)‖ ≤ (1 / 2 : ℝ) * secondBound :=
    (norm_half_bilinear_le _ _ (factor (projection value))).trans
      (mul_le_mul_of_nonneg_left secondSmall (by norm_num))
  apply (norm_bilinear_fiber_conjugate_le _ _ _).trans
  gcongr

end

end EulerNonuniqueness.General
