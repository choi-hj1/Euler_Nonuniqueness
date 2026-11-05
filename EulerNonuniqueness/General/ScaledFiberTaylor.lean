import EulerNonuniqueness.General.UniformLipschitzSecondTaylor

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_eventually_scaled_fiber_taylor
    (function : Space → Space) (quadratic : Space → BilinearEnd Space)
    (projection generator : Space →L[ℝ] Space) (coordinates : Space → Space →L[ℝ] Space)
    (continuous : ContinuousAt coordinates (0 : Space))
    (taylor : ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : Space,
      ‖base‖ + ‖increment‖ ≤ radius →
      ‖function (base + increment) - function base - fderiv ℝ function base increment -
        quadratic base increment increment‖ ≤ constant * ‖increment‖ ^ 3)
    (stationary : ∀ᶠ value in 𝓝 (0 : Space), function (projection value) = 0)
    (intertwines : ∀ᶠ value in 𝓝 (0 : Space),
      ∀ direction, fderiv ℝ function (projection value) (coordinates value direction) =
        coordinates value (generator direction)) :
    ∃ constant ≥ 0, ∀ᶠ value in 𝓝 (0 : Space),
      let relative := value - projection value
      ‖function (projection value + coordinates value relative) - coordinates value (generator relative) -
        quadratic (projection value) (coordinates value relative) (coordinates value relative)‖ ≤
          constant * ‖relative‖ ^ 3 := by
  obtain ⟨radius, positive, constant, nonnegative, estimate⟩ := taylor
  let bound := ‖coordinates 0‖ + 1
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have coordinateBound : ∀ᶠ value in 𝓝 (0 : Space), ‖coordinates value‖ ≤ bound := by
    have nearby := continuous.norm.eventually (gt_mem_nhds (show ‖coordinates (0 : Space)‖ < bound by
      dsimp only [bound]; linarith))
    exact nearby.mono fun value inside => inside.le
  have relativeContinuous : ContinuousAt (fun value : Space => value - projection value) 0 :=
    continuousAt_id.sub projection.continuous.continuousAt
  have evaluationContinuous : ContinuousAt (fun value : Space => coordinates value (value - projection value)) 0 :=
    isBoundedBilinearMap_apply.continuous.continuousAt.comp (continuous.prodMk relativeContinuous)
  have sizeContinuous : ContinuousAt
      (fun value : Space => ‖projection value‖ + ‖coordinates value (value - projection value)‖) 0 :=
    projection.continuous.continuousAt.norm.add evaluationContinuous.norm
  have sizeSmall : ∀ᶠ value in 𝓝 (0 : Space),
      ‖projection value‖ + ‖coordinates value (value - projection value)‖ ≤ radius := by
    have nearby := sizeContinuous.eventually (gt_mem_nhds (show
      ‖projection (0 : Space)‖ + ‖coordinates 0 (0 - projection 0)‖ < radius by simpa using positive))
    exact nearby.mono fun value inside => inside.le
  refine ⟨constant * bound ^ 3, by positivity, ?_⟩
  filter_upwards [stationary, intertwines, coordinateBound, sizeSmall] with value equilibrium conjugacy bounded inside
  dsimp only
  have actual := estimate (projection value) (coordinates value (value - projection value)) inside
  rw [equilibrium, sub_zero, conjugacy] at actual
  apply actual.trans
  calc
    constant * ‖coordinates value (value - projection value)‖ ^ 3 ≤
        constant * (bound * ‖value - projection value‖) ^ 3 := by
      gcongr
      exact (coordinates value).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right bounded (norm_nonneg _))
    _ = _ := by ring

end

end EulerNonuniqueness.General
