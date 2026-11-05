import EulerNonuniqueness.Section7.ActualSelectedDipoleObservationGeometry
import EulerNonuniqueness.Section7.ActualFiniteFamilySupport
import EulerNonuniqueness.Section7.SelectedDipoleFamilyAssembly
import EulerNonuniqueness.Section3.FinitePatchRestriction

noncomputable section

open MeasureTheory Set Filter Function Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000

theorem Scales.eventually_approximationData_of_actual_stopped_outgoing_cascades (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {factor threshold scaleRoot boundaryConstant referenceConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (thresholdSmall : threshold ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ truncations : ℕ → ℕ, Tendsto truncations atTop atTop →
    ∀ phase dipoleAngle : ℕ → ℕ → ℝ, ∀ shapeRadius monitor : ℕ → ℝ,
    ∀ prepared : (index : ℕ) → CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime
      (phase index) (dipoleAngle index) threshold referenceConstant scaleRoot (shapeRadius index) factor (monitor index)
      boundaryConstant (truncations index + 1),
    ∀ paths : (index : ℕ) → CascadeInternallyStoppedPath (prepared index),
    (∀ index, (paths index).stop = 1) →
    ∀ start initialDistance : ℕ → ℝ, ∀ direction : ℕ → ℂ,
    (∀ index, 0 ≤ start index) → (∀ index, start index ≤ 1 / 2) →
    (∀ index, 512 ≤ initialDistance index) →
    (∀ index, initialDistance index ≤ ({scales with frequency := frequency} : Scales).omega 1 / 16) →
    (∀ index, ‖direction index‖ = 1) →
    (∀ index, let motion := (prepared index).trajectory.movingFamily.patchMotion
      let outer : Fin (truncations index + 1) := ⟨0, by omega⟩
      let length := ({scales with frequency := frequency} : Scales).length 1
      ‖firstDipoleSeparation motion (start index) outer - (length : ℂ) * direction index‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (start index) outer - (length : ℂ) * (-direction index)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance index ≤
        (Complex.I * star (direction index) *
          (firstDipoleCenter motion (start index) outer - secondDipoleCenter motion (start index) outer)).re ∧
      ‖firstDipoleCenter motion (start index) outer - secondDipoleCenter motion (start index) outer‖ ≤
        (5 / 4 : ℝ) * length * initialDistance index) → Nonempty ApproximationData := by
  classical
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_actual_selected_dipole_observation_geometry amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall thresholdSmall rootPositive boundaryNonnegative referenceNonnegative,
    scales.eventually_actual_finite_family_support amplitudePositive ratioBound alphaPositive thresholdSmall
      referenceNonnegative] with frequency frequencyPositive geometry supportBound
  intro truncations truncationsTendsto phase dipoleAngle shapeRadius monitor prepared paths stopOne start initialDistance direction
    startNonnegative startSmall initialDistanceLarge initialDistanceSmall directionNorm outgoing
  let changed : Scales := {scales with frequency := frequency}
  let reference := fun index => (prepared index).referenceWitness.trajectory.movingFamily.patchMotion
  let alternative := fun index => (prepared index).trajectory.movingFamily.patchMotion
  let outer : (index : ℕ) → Fin (truncations index + 1) := fun _ => ⟨0, by omega⟩
  have observations (index : ℕ) := geometry (truncations index + 1) (phase index) (dipoleAngle index)
    (prepared index) (paths index) (stopOne index) (outer index) rfl (start index) (initialDistance index)
    (startNonnegative index) (startSmall index) (initialDistanceLarge index) (initialDistanceSmall index)
    (direction index) (directionNorm index) (outgoing index).1 (outgoing index).2.1
    (outgoing index).2.2.1 (outgoing index).2.2.2
  choose first chosen using observations
  have supported (index : ℕ) := supportBound (prepared index) (paths index) (outer index) rfl
  have initial (index : ℕ) : CascadeInitialDisks changed orbit sectionTime (dipoleAngle index)
      (reference index) (alternative index) := by
    simpa only [(prepared index).referenceIdentity] using (prepared index).commonInitial
  have alternativeEvolutions (index : ℕ) : FinitePatchEvolution changed (alternative index) 1 := by
    simpa only [stopOne index] using (paths index).evolution
  have disjoint (index : ℕ) : PatchesDisjoint (alternative index) 1 := by
    simpa only [stopOne index] using (paths index).patches_disjoint
  apply exists_approximationData_of_selected_dipole_cascade_families changed orbit sectionTime truncationsTendsto
    dipoleAngle reference alternative initial
    (fun index label => phase index (label.val + 1)) (fun index => (prepared index).referenceWitness.unstable)
    (fun index => (prepared index).referenceWitness.initial) (by linarith) amplitudePositive frequencyPositive
    (by change 1 < scales.ratio; linarith) alphaPositive
    (fun index => (prepared index).referenceWitness.evolution.mono (by norm_num)) alternativeEvolutions disjoint
    (radius := 5) (by norm_num) (fun index => (supported index).2)
    (fun index time inside => (supported index).1 time (by simpa only [stopOne index] using inside))
    outer (fun _ => rfl) (fun index => selectedDipolePatches (outer index) (first index))
    (fun index => selectedDipolePatches_outer (outer index) (first index))
    (fun index => selectedDipolePatches_card (outer index) (first index)) (changed.length_pos 1)
    (fun index => selectedDipoleCenter (alternative index) 1 (outer index) (first index))
    (fun index => (chosen index).1) (fun index => (chosen index).2.1)
    (fun index => (chosen index).2.2.1) (fun index => (chosen index).2.2.2)

end EulerNonuniqueness.Paper
