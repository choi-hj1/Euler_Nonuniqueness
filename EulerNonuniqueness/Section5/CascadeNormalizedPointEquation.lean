import EulerNonuniqueness.Section5.CascadeCenteredPointEquation
import EulerNonuniqueness.Section6.CenteredPointScaling

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def cascadeNormalizedPointPositions {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (start : ℝ) (rotation : ℂ) (time : ℝ) : FourPointConfiguration :=
  fun patch => ((scales.length (index.val + 1) : ℂ) * rotation)⁻¹ *
    fourPointCenterProjection (fun patch => patchCentroid motion
      (start + time / scales.omega (index.val + 1)) index patch) patch

def cascadeNormalizedPointForcing {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (start : ℝ) (rotation : ℂ) (time : ℝ) : FourPointConfiguration :=
  fun patch => ((scales.omega (index.val + 1) : ℂ) * ((scales.length (index.val + 1) : ℂ) * rotation))⁻¹ *
    quadrupoleCenteredForcing scales motion (start + time / scales.omega (index.val + 1)) index patch

namespace CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem normalizedPoint_equation (path : CascadeInternallyStoppedPath prepared)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (index : Fin count) (start time : ℝ) {rotation : ℂ} (rotationNorm : ‖rotation‖ = 1)
    (inside : start + time / scales.omega (index.val + 1) ∈ Icc 0 path.stop) :
    HasDerivAt
      (cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index start rotation)
      (fourPointCenteredField 1 (cascadeNormalizedPointPositions scales
          prepared.trajectory.movingFamily.patchMotion index start rotation time) +
        cascadeNormalizedPointForcing scales prepared.trajectory.movingFamily.patchMotion index start rotation time) time := by
  exact centered_point_normalized_hasDerivAt (scales.omega_pos frequencyPositive ratioPositive _)
    (scales.length_pos _) rotationNorm (path.centeredCentroid_point_equation inside index)

theorem normalizedPoint_pair_gap (path : CascadeInternallyStoppedPath prepared)
    (index : Fin count) (start time : ℝ) {rotation : ℂ} (rotationNorm : ‖rotation‖ = 1)
    (inside : start + time / scales.omega (index.val + 1) ∈ Icc 0 path.stop)
    (first second : Fin 4) (different : first ≠ second) :
    factor ≤ ‖cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index start rotation time first -
      cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index start rotation time second‖ := by
  have actual := path.internal_centroid_gap inside index first second different
  have positive := scales.length_pos (index.val + 1)
  simp only [cascadeNormalizedPointPositions, ← mul_sub, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive, rotationNorm, mul_one,
    fourPointCenterProjection] 
  have identity : (patchCentroid prepared.trajectory.movingFamily.patchMotion
      (start + time / scales.omega (index.val + 1)) index first -
        fourPointArithmeticCenter (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion
          (start + time / scales.omega (index.val + 1)) index patch)) -
      (patchCentroid prepared.trajectory.movingFamily.patchMotion
        (start + time / scales.omega (index.val + 1)) index second -
        fourPointArithmeticCenter (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion
          (start + time / scales.omega (index.val + 1)) index patch)) =
      patchCentroid prepared.trajectory.movingFamily.patchMotion (start + time / scales.omega (index.val + 1)) index first -
        patchCentroid prepared.trajectory.movingFamily.patchMotion (start + time / scales.omega (index.val + 1)) index second := by abel
  rw [identity]
  exact (le_div_iff₀ positive).mpr actual |>.trans_eq (by ring)

end CascadeInternallyStoppedPath

end EulerNonuniqueness.Paper
