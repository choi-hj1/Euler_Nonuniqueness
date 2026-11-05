import EulerNonuniqueness.Section5.CascadeStoppedBoundaryLabelGaps
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_stopped_cascade_boundary_label_gaps (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant factor : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    (∀ index : Fin count,
      boundaryConstant / (scaleRoot ^ 2 * ({scales with frequency := frequency} : Scales).omega (index.val + 1) ^ 2) ≤ 1) ∧
    ∀ time ∈ Icc 0 path.stop, ∀ receiver source : Fin count, ∀ first second : Fin 4,
      (receiver, first) ≠ (source, second) →
      8 * ({scales with frequency := frequency} : Scales).radius (receiver.val + 1) +
        8 * ({scales with frequency := frequency} : Scales).radius (source.val + 1) <
        dist (prepared.trajectory.movingFamily.patchMotion.boundary time receiver first 0)
          (prepared.trajectory.movingFamily.patchMotion.boundary time source second 0) := by
  have boundaryLimit : Tendsto (fun frequency : ℝ => (boundaryConstant / scaleRoot ^ 2) * frequency⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul
      (boundaryConstant / scaleRoot ^ 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := factor) (bound := 3) factorPositive factorSmall (by norm_num),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    boundaryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyPositive internalGeometry locationGeometry boundarySmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius monitor count prepared path
  let changed : Scales := {scales with frequency := frequency}
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have radii (index : Fin count) : 0 < changed.radius (index.val + 1) :=
    changed.radius_pos amplitudePositive frequencyPositive ratioPositive _
  have boundary (index : Fin count) : boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2) ≤ 1 := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) (index.val + 1)
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) (inv_anti₀ frequencyPositive omegaBound) 2
    have actual := (mul_le_mul_of_nonneg_left inverseBound
      (show 0 ≤ boundaryConstant / scaleRoot ^ 2 by positivity)).trans boundarySmall.le
    convert actual using 1
    field_simp [rootPositive.ne', omegaPositive.ne']
    <;> ring
  refine ⟨boundary, ?_⟩
  intro time inside receiver source first second different
  apply path.boundary_label_gaps_of_radius_bounds radii
    (fun index => (internalGeometry (index.val + 1)).2.1) ?_ boundary inside receiver source first second different
  intro index
  have radius := (locationGeometry (index.val + 1)).2.1
  have length := (locationGeometry (index.val + 1)).2.2.1
  simp only [one_mul] at radius
  linarith [changed.location_pos (index.val + 1)]

end EulerNonuniqueness.Paper
