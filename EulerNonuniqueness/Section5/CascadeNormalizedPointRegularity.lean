import EulerNonuniqueness.Section5.CascadeNormalizedPointEquation
import EulerNonuniqueness.Section5.CascadeNeutralVelocity
import EulerNonuniqueness.Section6.CenteredPointPassageStability

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

namespace CascadeMaterialPreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count)

def normalizedPointVelocity (index : Fin count) (start : ℝ) (rotation : ℂ) (time : ℝ) : FourPointConfiguration :=
  fun patch => ((scales.length (index.val + 1) : ℂ) * rotation)⁻¹ *
    ((scales.omega (index.val + 1) : ℂ)⁻¹ * fourPointCenterProjection
      (fun label => (prepared.trajectory.velocity (start + time / scales.omega (index.val + 1))).2.1
        (finProdFinEquiv (index, label))) patch)

theorem normalizedPointVelocity_continuous (index : Fin count) (start : ℝ) (rotation : ℂ) :
    Continuous (prepared.normalizedPointVelocity index start rotation) := by
  have point (patch : Fin 4) : Continuous (fun time =>
      (prepared.trajectory.velocity (start + time / scales.omega (index.val + 1))).2.1
        (finProdFinEquiv (index, patch))) :=
    (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp
      (prepared.trajectory.velocity_continuous.comp (continuous_const.add (continuous_id.div_const _)))))
  have points := continuous_pi fun patch => point patch
  have centered := fourPointCenterProjection_lipschitz.continuous.comp points
  exact continuous_pi fun patch => continuous_const.mul
    (continuous_const.mul ((continuous_apply patch).comp centered))

theorem normalizedPoint_hasDerivAt_velocity (index : Fin count) (start time : ℝ) (rotation : ℂ)
    (inside : start + time / scales.omega (index.val + 1) ∈ Ioo (-(1 : ℝ)) 3) :
    HasDerivAt (cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index start rotation)
      (prepared.normalizedPointVelocity index start rotation time) time := by
  have point (patch : Fin 4) : HasDerivAt
      (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
      ((prepared.trajectory.velocity (start + time / scales.omega (index.val + 1))).2.1
        (finProdFinEquiv (index, patch))) (start + time / scales.omega (index.val + 1)) := by
    apply (prepared.trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) _).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) member index patch).symm
  have centered := fourPointCenterProjection_hasDerivAt (hasDerivAt_pi.mpr point)
  apply hasDerivAt_pi.mpr
  intro patch
  have derivative := ((hasDerivAt_pi.mp centered patch).scomp time
    (((hasDerivAt_id time).div_const (scales.omega (index.val + 1))).const_add start)).const_mul
      (((scales.length (index.val + 1) : ℂ) * rotation)⁻¹)
  simpa only [cascadeNormalizedPointPositions, normalizedPointVelocity, Function.comp_def,
    Complex.real_smul, one_div, Complex.ofReal_inv] using derivative

end CascadeMaterialPreparedPair

namespace CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem normalizedPoint_continuousOn (path : CascadeInternallyStoppedPath prepared)
    (index : Fin count) (start : ℝ) (rotation : ℂ) {times : Set ℝ}
    (inside : ∀ time ∈ times, start + time / scales.omega (index.val + 1) ∈ Icc 0 path.stop) :
    ContinuousOn (cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index start rotation) times := by
  intro time member
  have actual := inside time member
  exact (prepared.normalizedPoint_hasDerivAt_velocity index start time rotation
    ⟨by linarith [actual.1], by linarith [actual.2, path.stopBound]⟩).continuousAt.continuousWithinAt

theorem normalizedPointForcing_continuousOn (path : CascadeInternallyStoppedPath prepared)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (factorPositive : 0 < factor) (index : Fin count) (start : ℝ) {rotation : ℂ}
    (rotationNorm : ‖rotation‖ = 1) {times : Set ℝ}
    (inside : ∀ time ∈ times, start + time / scales.omega (index.val + 1) ∈ Icc 0 path.stop) :
    ContinuousOn (cascadeNormalizedPointForcing scales prepared.trajectory.movingFamily.patchMotion index start rotation) times := by
  have positions := path.normalizedPoint_continuousOn index start rotation inside
  have field : ContinuousOn (fun time => fourPointCenteredField 1
      (cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index start rotation time)) times := by
    apply fourPointCenterProjection_lipschitz.continuous.comp_continuousOn
    intro time member
    apply (fourPointField_contDiffAt 1 (fun target source different =>
      norm_pos_iff.mp (factorPositive.trans_le
        (path.normalizedPoint_pair_gap index start time rotationNorm (inside time member) target source different.symm)))).continuousAt.comp_continuousWithinAt
    exact positions time member
  apply ((prepared.normalizedPointVelocity_continuous index start rotation).continuousOn.sub field).congr
  intro time member
  have actual := inside time member
  have velocity := prepared.normalizedPoint_hasDerivAt_velocity index start time rotation
    ⟨by linarith [actual.1], by linarith [actual.2, path.stopBound]⟩
  have equation := path.normalizedPoint_equation frequencyPositive ratioPositive index start time rotationNorm actual
  have equality := velocity.unique equation
  exact (sub_eq_iff_eq_add.mpr (equality.trans (add_comm _ _))).symm

end CascadeInternallyStoppedPath

end EulerNonuniqueness.Paper
