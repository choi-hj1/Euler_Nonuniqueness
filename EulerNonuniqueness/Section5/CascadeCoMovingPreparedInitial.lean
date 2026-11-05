import EulerNonuniqueness.Section5.CascadeCoMovingPreparedPair
import EulerNonuniqueness.Section5.CascadeCoMovingInitialMonitors

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem CascadeCoMovingPreparedPair.initial_comoving_monitors
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeCoMovingPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) :
    (∀ label, cascadeExtentMonitor scales label (prepared.trajectory.movingFamily.cascadeCenters 0) < 0) ∧
    (∀ first second, cascadeAnchorLowerMonitor scales first second
      (prepared.trajectory.movingFamily.cascadeCenters 0) < 0) ∧
    (∀ first second, cascadeAnchorUpperMonitor scales first second
      (prepared.trajectory.movingFamily.cascadeCenters 0) < 0) ∧
    (∀ index, cascadeAnchorNormMonitor index (prepared.trajectory.movingFamily.cascadeCenters 0) < 0) := by
  have centers : prepared.trajectory.movingFamily.cascadeCenters 0 =
      cascadeInitialCenter scales orbit sectionTime (fun index => phase (index.val + 1))
        prepared.unstable (dipoleAngle count) := by
    funext label
    change prepared.trajectory.center (finProdFinEquiv label) 0 = _
    rw [prepared.trajectory.center_eq_curve (by norm_num), prepared.trajectory.initial_identity]
    exact congrArg (cascadeInitialCenter scales orbit sectionTime (fun index => phase (index.val + 1))
      prepared.unstable (dipoleAngle count)) (Equiv.symm_apply_apply finProdFinEquiv label)
  rw [centers]
  refine ⟨?_, cascadeAnchorMonitors_initial_strict scales orbit sectionTime _ prepared.unstable _⟩
  intro label
  apply cascadeExtentMonitor_initial_of_offset
  have initial := prepared.initialLocation label
  rw [prepared.trajectory.initial_identity] at initial
  simpa only [cascadeLocationMonitor, Equiv.symm_apply_apply, sub_neg] using initial

end EulerNonuniqueness.Paper
