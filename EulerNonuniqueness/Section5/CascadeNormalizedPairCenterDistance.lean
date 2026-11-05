import EulerNonuniqueness.Section5.CascadeNormalizedPointEquation
import EulerNonuniqueness.Section7.QuadrupoleAnnulus

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPoint_pair_center_distance_abs_sub_le (first second : FourPointConfiguration) :
    |‖(first 0 + first 3) / 2 - (first 1 + first 2) / 2‖ -
      ‖(second 0 + second 3) / 2 - (second 1 + second 2) / 2‖| ≤ 2 * ‖first - second‖ := by
  have component (patch : Fin 4) : ‖first patch - second patch‖ ≤ ‖first - second‖ :=
    norm_le_pi_norm (first - second) patch
  have identity : ((first 0 + first 3) / 2 - (first 1 + first 2) / 2) -
      ((second 0 + second 3) / 2 - (second 1 + second 2) / 2) =
      ((first 0 - second 0) + (first 3 - second 3) - (first 1 - second 1) - (first 2 - second 2)) / 2 := by ring
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [identity, norm_div]
  norm_num
  have firstTriangle := norm_add_le (first 0 - second 0) (first 3 - second 3)
  have secondTriangle := norm_sub_le ((first 0 - second 0) + (first 3 - second 3)) (first 1 - second 1)
  have thirdTriangle := norm_sub_le ((first 0 - second 0) + (first 3 - second 3) - (first 1 - second 1))
    (first 2 - second 2)
  nlinarith only [firstTriangle, secondTriangle, thirdTriangle, component 0, component 1, component 2, component 3]

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem cascadeNormalizedPointPositions_pair_center_distance {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (index : Fin count) (start time : ℝ) {rotation : ℂ}
    (rotationNorm : ‖rotation‖ = 1) :
    let positions := cascadeNormalizedPointPositions scales motion index start rotation time
    ‖(positions 0 + positions 3) / 2 - (positions 1 + positions 2) / 2‖ =
      pairCenterDistance motion (start + time / scales.omega (index.val + 1)) index /
        scales.length (index.val + 1) := by
  dsimp only
  have identity :
      (cascadeNormalizedPointPositions scales motion index start rotation time 0 +
        cascadeNormalizedPointPositions scales motion index start rotation time 3) / 2 -
      (cascadeNormalizedPointPositions scales motion index start rotation time 1 +
        cascadeNormalizedPointPositions scales motion index start rotation time 2) / 2 =
      ((scales.length (index.val + 1) : ℂ) * rotation)⁻¹ *
        ((patchCentroid motion (start + time / scales.omega (index.val + 1)) index 0 +
            patchCentroid motion (start + time / scales.omega (index.val + 1)) index 3) / 2 -
          (patchCentroid motion (start + time / scales.omega (index.val + 1)) index 1 +
            patchCentroid motion (start + time / scales.omega (index.val + 1)) index 2) / 2) := by
    dsimp only [cascadeNormalizedPointPositions, fourPointCenterProjection]
    ring
  rw [identity, norm_mul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (scales.length_pos _), rotationNorm, mul_one]
  change (scales.length (index.val + 1))⁻¹ * pairCenterDistance motion
    (start + time / scales.omega (index.val + 1)) index = _
  ring

theorem cascadeNormalizedPointPositions_pair_center_shadow_error {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (index : Fin count) (start time incomingTime : ℝ)
    (orbit : SeparatingOrbit) {rotation : ℂ} (rotationNorm : ‖rotation‖ = 1) :
    |pairCenterDistance motion (start + time / scales.omega (index.val + 1)) index /
        scales.length (index.val + 1) - separationRadius orbit (time + incomingTime)| ≤
      2 * ‖cascadeNormalizedPointPositions scales motion index start rotation time -
        centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime))‖ := by
  have referenceIdentity :
      ‖(centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime)) 0 +
          centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime)) 3) / 2 -
        (centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime)) 1 +
          centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime)) 2) / 2‖ =
        separationRadius orbit (time + incomingTime) := by
    change ‖(orbit.positive (time + incomingTime) - orbit.negative (time + incomingTime)) / 2 -
      (-orbit.positive (time + incomingTime) + orbit.negative (time + incomingTime)) / 2‖ =
        ‖orbit.positive (time + incomingTime) - orbit.negative (time + incomingTime)‖
    congr 1
    ring
  have actual := fourPoint_pair_center_distance_abs_sub_le
    (cascadeNormalizedPointPositions scales motion index start rotation time)
    (centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime)))
  rw [cascadeNormalizedPointPositions_pair_center_distance scales motion index start time rotationNorm, referenceIdentity] at actual
  exact actual

end EulerNonuniqueness.Paper

