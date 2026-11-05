import EulerNonuniqueness.Section6.SourcePacketPostHitRadius

noncomputable section

open Set Metric Filter
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_posthit_width_and_radius (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → horizon ≤ 1 →
    start + horizon ≤ path.stop → 512 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency}).omega (index.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := ({scales with frequency := frequency}).length (index.val + 1)
    let omega : ℝ := ({scales with frequency := frequency}).omega (index.val + 1)
    ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start index - secondDipoleCenter motion start index)).re →
    ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ elapsed ∈ Icc 0 horizon,
      ‖firstDipoleSeparation motion (start + elapsed) index‖ ≤ 2 * length ∧
      ‖secondDipoleSeparation motion (start + elapsed) index‖ ≤ 2 * length ∧
      (∀ patch, ‖patchCentroid motion (start + elapsed) index patch -
        quadrupoleCenter motion (start + elapsed) index‖ ≤ 4 * omega * length) ∧
      (∀ patch, motion.domain (start + elapsed) index patch ⊆
        closedBall (quadrupoleCenter motion (start + elapsed) index) (4 * omega * length)) := by
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyLarge continuation geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start horizon initialDistance
    startNonnegative horizonNonnegative horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper elapsed inside
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := by change 0 < frequency; linarith
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have tracking := continuation count phase dipoleAngle prepared path index start horizon initialDistance
    startNonnegative horizonNonnegative horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper elapsed inside
  have globalInside : start + elapsed ∈ Ioo (-(1 : ℝ)) 3 := by
    constructor <;> linarith [inside.1, inside.2, path.stopBound]
  have radiusSmall : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    have first := (geometry (index.val + 1)).2.1
    have second := mul_le_of_le_one_left (changed.length_pos (index.val + 1)).le factorSmall
    linarith
  exact source_packet_posthit_width_and_radius motion index (start + elapsed)
    (changed.length_pos (index.val + 1))
    (frequencyLarge.trans (changed.omega_ge_frequency frequencyPositive (by linarith) (index.val + 1)))
    (inside.2.trans horizonUpper) initialDistanceSmall directionNorm tracking.1 tracking.2.1 tracking.2.2.2
    (Real.sqrt_nonneg _) radiusSmall
    (fun patch => prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl)
      globalInside index patch)

end EulerNonuniqueness.Paper

