import EulerNonuniqueness.Section6.SourcePacketActualPostHitContinuation
import EulerNonuniqueness.Section7.QuadrupoleAnnulus

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def dipoleCenterForPatch {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4) : ℂ :=
  if patch = 0 ∨ patch = 3 then firstDipoleCenter motion time index else secondDipoleCenter motion time index

theorem patchCentroid_distance_dipoleCenterForPatch {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    ‖patchCentroid motion time index patch - dipoleCenterForPatch motion time index patch‖ =
      if patch = 0 ∨ patch = 3 then ‖firstDipoleSeparation motion time index‖ / 2 else ‖secondDipoleSeparation motion time index‖ / 2 := by
  have firstIdentity (first second : ℂ) : ‖first - (first + second) / 2‖ = ‖first - second‖ / 2 := by
    rw [show first - (first + second) / 2 = (first - second) / 2 by ring, norm_div]
    norm_num
  have secondIdentity (first second : ℂ) : ‖second - (first + second) / 2‖ = ‖first - second‖ / 2 := by
    rw [show second - (first + second) / 2 = -(first - second) / 2 by ring, norm_div, norm_neg]
    norm_num
  fin_cases patch <;> simp only [dipoleCenterForPatch, firstDipoleCenter, secondDipoleCenter,
    firstDipoleSeparation, secondDipoleSeparation] <;> norm_num
  · exact firstIdentity _ _
  · exact firstIdentity _ _
  · exact secondIdentity _ _
  · exact secondIdentity _ _

theorem dipole_separation_sharp_norm_bounds {length : ℝ} (lengthPositive : 0 < length) {direction separation : ℂ}
    (directionNorm : ‖direction‖ = 1) (tracked : ‖separation - (length : ℂ) * direction‖ ≤ length / 16) :
    15 * length / 16 ≤ ‖separation‖ ∧ ‖separation‖ ≤ 17 * length / 16 := by
  have idealNorm : ‖(length : ℂ) * direction‖ = length := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, directionNorm, mul_one]
  have upper := norm_add_le (separation - (length : ℂ) * direction) ((length : ℂ) * direction)
  have lower := norm_add_le ((length : ℂ) * direction - separation) separation
  rw [sub_add_cancel, idealNorm] at upper
  rw [sub_add_cancel, norm_sub_rev, idealNorm] at lower
  constructor <;> linarith

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_outgoing_pair_domain_annuli (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → horizon ≤ 1 → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (index.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (index.val + 1)
    ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start index - secondDipoleCenter motion start index)).re →
    ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ elapsed ∈ Icc 0 horizon, ∀ patch position, position ∈ motion.domain (start + elapsed) index patch →
      length / 3 ≤ ‖position - dipoleCenterForPatch motion (start + elapsed) index patch‖ ∧
        ‖position - dipoleCenterForPatch motion (start + elapsed) index patch‖ ≤ 3 * length / 4 := by
  filter_upwards [scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency tracking geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start horizon initialDistance startNonnegative
    horizonNonnegative horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper elapsed inside patch position positionInside
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have tracked := tracking count phase dipoleAngle prepared path index start horizon initialDistance startNonnegative horizonNonnegative
    horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm firstInitial secondInitial initialProjection initialUpper elapsed inside
  have firstBounds := dipole_separation_sharp_norm_bounds lengthPositive directionNorm tracked.1
  have secondBounds := dipole_separation_sharp_norm_bounds lengthPositive (show ‖-direction‖ = 1 by simpa using directionNorm) tracked.2.1
  have centroidDistance := patchCentroid_distance_dipoleCenterForPatch motion (start + elapsed) index patch
  have centroidBounds : 15 * length / 32 ≤ ‖patchCentroid motion (start + elapsed) index patch - dipoleCenterForPatch motion (start + elapsed) index patch‖ ∧
      ‖patchCentroid motion (start + elapsed) index patch - dipoleCenterForPatch motion (start + elapsed) index patch‖ ≤ 17 * length / 32 := by
    rw [centroidDistance]
    split_ifs <;> constructor <;> linarith
  have timeInside : start + elapsed ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have domain := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl) timeInside index patch positionInside
  rw [Metric.mem_closedBall, dist_eq_norm] at domain
  have radiusSmall := (geometry (index.val + 1)).2.1
  change changed.radius (index.val + 1) ≤ 1 * length / 1000 at radiusSmall
  have upper := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion (start + elapsed) index patch)
    (dipoleCenterForPatch motion (start + elapsed) index patch)
  have lower := norm_sub_le_norm_sub_add_norm_sub (patchCentroid motion (start + elapsed) index patch) position
    (dipoleCenterForPatch motion (start + elapsed) index patch)
  rw [norm_sub_rev (patchCentroid motion (start + elapsed) index patch) position] at lower
  constructor <;> linarith [centroidBounds.1, centroidBounds.2]

end EulerNonuniqueness.Paper
