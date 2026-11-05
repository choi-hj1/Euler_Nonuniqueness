import EulerNonuniqueness.Section5.CascadeRelativeCenterHistory
import EulerNonuniqueness.Section5.CascadeFirstMomentSourceDefect

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem relative_center_retained_history
    (path : CascadeInternallyStoppedPath prepared) (index : Fin count)
    {start finish : ℝ} (startNonnegative : 0 ≤ start) (ordered : start ≤ finish) (finishBound : finish ≤ path.stop) :
    let center := fun time => quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
      quadrupoleCenter prepared.reference time index
    let velocity := fun time => prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time
    IntervalIntegrable velocity volume start finish ∧
      IntervalIntegrable (fun time => ‖velocity time‖ / scales.location (index.val + 1)) volume start finish ∧
      center finish = center start + ∫ time in start..finish, velocity time ∧
      ‖center finish‖ / scales.location (index.val + 1) ≤
        ‖center start‖ / scales.location (index.val + 1) +
          ∫ time in start..finish, ‖velocity time‖ / scales.location (index.val + 1) := by
  dsimp only
  let center := fun time => quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
    quadrupoleCenter prepared.reference time index
  let velocity := fun time => prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time
  have velocityContinuous : Continuous velocity :=
    (prepared.pairedCenterVelocity_continuous 0 index).sub (prepared.pairedCenterVelocity_continuous 1 index)
  have velocityIntegrable : IntervalIntegrable velocity volume start finish := velocityContinuous.intervalIntegrable _ _
  have normIntegrable : IntervalIntegrable (fun time => ‖velocity time‖ / scales.location (index.val + 1))
      volume start finish := velocityIntegrable.norm.div_const _
  have derivative (time : ℝ) (inside : time ∈ Icc start finish) : HasDerivAt center (velocity time) time := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
    exact (prepared.paired_center_hasDerivAt 0 index globalInside).sub
      (prepared.paired_center_hasDerivAt 1 index globalInside)
  have integralIdentity : (∫ time in start..finish, velocity time) = center finish - center start :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered
      (fun time inside => (derivative time inside).continuousAt.continuousWithinAt)
      (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩) velocityIntegrable
  have retained : center finish = center start + ∫ time in start..finish, velocity time := by
    rw [integralIdentity]
    abel
  have normBound : ‖center finish‖ ≤ ‖center start‖ + ∫ time in start..finish, ‖velocity time‖ := by
    rw [retained]
    exact (norm_add_le _ _).trans (add_le_add_left
      (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := start) (b := finish)
        (f := velocity) ordered) _)
  have divided := div_le_div_of_nonneg_right normBound (scales.location_pos (index.val + 1)).le
  rw [add_div, ← intervalIntegral.integral_div] at divided
  exact ⟨velocityIntegrable, normIntegrable, retained, divided⟩

theorem relative_firstMoment_retained_history
    (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    {start finish : ℝ} (startNonnegative : 0 ≤ start) (ordered : start ≤ finish) (finishBound : finish ≤ path.stop) :
    let moment := relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index
    let velocity := relativeFirstMomentExternalVelocity scales prepared.trajectory.movingFamily.patchMotion prepared.reference index
    IntervalIntegrable velocity volume start finish ∧
      IntervalIntegrable (fun time => ‖velocity time‖) volume start finish ∧
      moment finish = moment start + ∫ time in start..finish, velocity time ∧
      ‖moment finish‖ ≤ ‖moment start‖ + ∫ time in start..finish, ‖velocity time‖ := by
  dsimp only
  let moment := relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let velocity := relativeFirstMomentExternalVelocity scales prepared.trajectory.movingFamily.patchMotion prepared.reference index
  have subset : Icc start finish ⊆ Icc 0 path.stop :=
    fun time inside => ⟨startNonnegative.trans inside.1, inside.2.trans finishBound⟩
  have velocityContinuous : ContinuousOn velocity (Icc start finish) :=
    (path.relativeFirstMomentExternalVelocity_continuousOn amplitudePositive frequencyPositive ratioPositive index).mono subset
  have velocityIntegrable : IntervalIntegrable velocity volume start finish :=
    velocityContinuous.intervalIntegrable_of_Icc (μ := volume) ordered
  have normIntegrable : IntervalIntegrable (fun time => ‖velocity time‖) volume start finish := velocityIntegrable.norm
  have derivative (time : ℝ) (inside : time ∈ Icc start finish) : HasDerivAt moment (velocity time) time := by
    simpa only [velocity, relativeFirstMomentExternalVelocity] using
      path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
  have integralIdentity : (∫ time in start..finish, velocity time) = moment finish - moment start :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered
      (fun time inside => (derivative time inside).continuousAt.continuousWithinAt)
      (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩) velocityIntegrable
  have retained : moment finish = moment start + ∫ time in start..finish, velocity time := by
    rw [integralIdentity]
    abel
  have normBound : ‖moment finish‖ ≤ ‖moment start‖ + ∫ time in start..finish, ‖velocity time‖ := by
    rw [retained]
    exact (norm_add_le _ _).trans (add_le_add_left
      (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := start) (b := finish)
        (f := velocity) ordered) _)
  exact ⟨velocityIntegrable, normIntegrable, retained, normBound⟩

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
