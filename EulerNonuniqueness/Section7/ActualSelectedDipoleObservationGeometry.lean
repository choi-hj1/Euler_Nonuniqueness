import EulerNonuniqueness.Section7.DipoleSelectionGeometry
import EulerNonuniqueness.Section7.ActualMacroCenterDrift
import EulerNonuniqueness.Section7.ReferenceObservationGeometry

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000

theorem Scales.eventually_actual_selected_dipole_observation_geometry (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {factor threshold scaleRoot boundaryConstant referenceConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (thresholdSmall : threshold ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, path.stop = 1 → ∀ outer : Fin count, outer.val = 0 →
    ∀ start initialDistance : ℝ, 0 ≤ start → start ≤ 1 / 2 → 512 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency} : Scales).omega 1 / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length 1
    ‖firstDipoleSeparation motion start outer - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start outer - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start outer - secondDipoleCenter motion start outer)).re →
    ‖firstDipoleCenter motion start outer - secondDipoleCenter motion start outer‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∃ first : Bool,
      ‖selectedDipoleCenter motion 1 outer first‖ ≤ 2 ∧
      (∀ index patch position, position ∈ reference.domain 1 index patch →
        4 * length ≤ ‖position - selectedDipoleCenter motion 1 outer first‖) ∧
      (∀ pair ∈ selectedDipolePatches outer first, ∀ position, position ∈ motion.domain 1 pair.1 pair.2 →
        length / 3 ≤ ‖position - selectedDipoleCenter motion 1 outer first‖ ∧
          ‖position - selectedDipoleCenter motion 1 outer first‖ ≤ 3 * length / 4) ∧
      ∀ pair ∉ selectedDipolePatches outer first, ∀ position, position ∈ motion.domain 1 pair.1 pair.2 →
        4 * length ≤ ‖position - selectedDipoleCenter motion 1 outer first‖ := by
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_actual_outgoing_pair_domain_annuli amplitudePositive ratioBound alphaPositive orbit sectionTime factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_actual_macro_center_drift amplitudePositive ratioBound alphaPositive factorPositive factorSmall rootPositive boundaryNonnegative
      (budget := scales.location 1 / 100) (div_pos (scales.location_pos 1) (by norm_num)),
    scales.eventually_reference_observation_geometry amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency frequencyLarge tracking pairDomains macroDrift referenceGeometry geometry
  intro count phase dipoleAngle shapeRadius monitor prepared path stopOne outer outerZero start initialDistance startNonnegative startSmall
    initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let length := changed.length 1
  let horizon := 1 - start
  let scale := changed.location 1
  have scalePositive : 0 < scale := changed.location_pos 1
  have lengthPositive : 0 < length := changed.length_pos 1
  have frequencyPositive : 0 < changed.frequency := by change 0 < frequency; linarith
  have omegaLarge : 64 ≤ changed.omega 1 := frequencyLarge.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) 1)
  have horizonLower : 1 / 2 ≤ horizon := by dsimp only [horizon]; linarith
  have horizonUpper : horizon ≤ 1 := by dsimp only [horizon]; linarith
  have horizonNonnegative : 0 ≤ horizon := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans horizonLower
  have endIdentity : start + horizon = 1 := by dsimp only [horizon]; ring
  have endBound : start + horizon ≤ path.stop := by rw [endIdentity, stopOne]
  have timeInside : 1 ∈ Icc 0 path.stop := by rw [stopOne]; norm_num
  have omegaIndex : changed.omega (outer.val + 1) = changed.omega 1 := by rw [outerZero, zero_add]
  have lengthIndex : changed.length (outer.val + 1) = length := by simp only [outerZero, zero_add, length]
  have tracked := tracking count phase dipoleAngle prepared path outer start horizon initialDistance startNonnegative horizonNonnegative horizonUpper
    endBound initialDistanceLarge (by simpa only [outerZero, zero_add] using initialDistanceSmall) direction directionNorm
    (by simpa only [outerZero, zero_add] using firstInitial) (by simpa only [outerZero, zero_add] using secondInitial)
    (by simpa only [outerZero, zero_add] using initialProjection) (by simpa only [outerZero, zero_add] using initialUpper) horizon ⟨horizonNonnegative, le_rfl⟩
  rw [endIdentity, lengthIndex, omegaIndex] at tracked
  have domains := pairDomains count phase dipoleAngle prepared path outer start horizon initialDistance startNonnegative horizonNonnegative horizonUpper
    endBound initialDistanceLarge (by simpa only [outerZero, zero_add] using initialDistanceSmall) direction directionNorm
    (by simpa only [outerZero, zero_add] using firstInitial) (by simpa only [outerZero, zero_add] using secondInitial)
    (by simpa only [outerZero, zero_add] using initialProjection) (by simpa only [outerZero, zero_add] using initialUpper) horizon ⟨horizonNonnegative, le_rfl⟩
  rw [endIdentity, lengthIndex] at domains
  have pairGap : 24 * length ≤ ‖firstDipoleCenter motion 1 outer - secondDipoleCenter motion 1 outer‖ := by
    have duration := mul_le_mul_of_nonneg_left horizonLower (show 0 ≤ (3 / 4 : ℝ) * length * changed.omega 1 by positivity)
    have omegaLength := mul_le_mul_of_nonneg_right omegaLarge lengthPositive.le
    have positiveInitial := mul_le_mul_of_nonneg_left (show 0 ≤ initialDistance by linarith)
      (show 0 ≤ (3 / 4 : ℝ) * length by positivity)
    nlinarith [tracked.2.2.1]
  obtain ⟨first, farCenter⟩ := exists_selectedDipoleCenter_far motion 1 outer (changed.location 1 : ℂ)
  let center := selectedDipoleCenter motion 1 outer first
  have centerFar : 12 * length ≤ ‖center - (changed.location 1 : ℂ)‖ := by linarith
  have nearAlternative : ‖center - quadrupoleCenter motion 1 outer‖ ≤ scale / 100 := by
    apply selectedDipoleCenter_near_quadcenter motion 1 outer first
    intro patch
    simpa only [outerZero, zero_add] using (path.centroid_extent timeInside outer patch).le
  have macroBound := macroDrift prepared path 1 timeInside outer
  simp only [outerZero, zero_add, mul_one] at macroBound
  change ‖quadrupoleCenter motion 1 outer - (changed.location 1 : ℂ)‖ ≤ scale / 100 at macroBound
  have referenceData := referenceGeometry prepared.referenceWitness 1 ⟨zero_le_one, le_rfl⟩
  have referenceOuter := referenceData.2 outer outerZero
  have referenceCenter : ‖quadrupoleCenter reference 1 outer - (changed.location 1 : ℂ)‖ ≤ length := referenceOuter.1
  have lengthSmall : length ≤ scale / 1000 := (geometry 1).2.2.1
  have nearReference : ‖center - quadrupoleCenter reference 1 outer‖ ≤ scale / 16 := by
    have first := norm_sub_le_norm_sub_add_norm_sub center (quadrupoleCenter motion 1 outer) (changed.location 1 : ℂ)
    have second := norm_sub_le_norm_sub_add_norm_sub center (changed.location 1 : ℂ) (quadrupoleCenter reference 1 outer)
    rw [norm_sub_rev (changed.location 1 : ℂ) (quadrupoleCenter reference 1 outer)] at second
    linarith
  have ownAlternative (index : Fin count) (patch : Fin 4) (position : ℂ) (inside : position ∈ motion.domain 1 index patch) :
      ‖position - quadrupoleCenter motion 1 index‖ ≤ scale / 50 := by
    have domain := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl) (by norm_num) index patch inside
    rw [mem_closedBall, dist_eq_norm] at domain
    have extent := (path.centroid_extent timeInside index patch).le
    have radius := (geometry (index.val + 1)).2.2.2
    have location := changed.location_antitone (show 1 ≤ index.val + 1 by omega)
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion 1 index patch) (quadrupoleCenter motion 1 index)
    linarith
  have ownReference (index : Fin count) (patch : Fin 4) (position : ℂ) (inside : position ∈ reference.domain 1 index patch) :
      ‖position - quadrupoleCenter reference 1 index‖ ≤ scale / 50 := by
    have own := referenceData.1 index patch position inside
    have small := (geometry (index.val + 1)).2.2.1
    have location := changed.location_antitone (show 1 ≤ index.val + 1 by omega)
    linarith
  have initialGap (other : Fin count) (different : other ≠ outer) : scale / 2 ≤
      |changed.location (outer.val + 1) - changed.location (other.val + 1)| := by
    have otherPositive : 1 < other.val + 1 := by
      have values : other.val ≠ outer.val := fun equality => different (Fin.ext equality)
      omega
    have location := changed.location_le_half_of_lt otherPositive
    rw [outerZero, zero_add]
    exact (show scale / 2 ≤ changed.location 1 - changed.location (other.val + 1) by linarith).trans (le_abs_self _)
  have alternativeSeparation (other : Fin count) (different : other ≠ outer) : scale / 4 ≤
      ‖quadrupoleCenter motion 1 outer - quadrupoleCenter motion 1 other‖ := by
    have bound := (path.quadrupole_pair_bounds timeInside outer other different.symm).1
    linarith [initialGap other different]
  have referenceSeparation (other : Fin count) (different : other ≠ outer) : scale / 4 ≤
      ‖quadrupoleCenter reference 1 outer - quadrupoleCenter reference 1 other‖ := by
    have bound := (prepared.referenceWitness.coarse.2.2 1 (by norm_num) outer other different.symm).1
    linarith [initialGap other different]
  refine ⟨first, ?_, ?_, ?_, ?_⟩
  · have close := norm_sub_le_norm_sub_add_norm_sub center (quadrupoleCenter motion 1 outer) (changed.location 1 : ℂ)
    have triangle := norm_add_le (center - (changed.location 1 : ℂ)) (changed.location 1 : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos scalePositive] at triangle
    change ‖center‖ ≤ 2
    linarith [changed.location_le_one 1]
  · intro index patch position inside
    change 4 * length ≤ ‖position - center‖
    by_cases same : index = outer
    · subst index
      have bound := referenceOuter.2 patch position inside
      change ‖position - (changed.location 1 : ℂ)‖ ≤ 5 * length at bound
      have triangle := norm_sub_le_norm_sub_add_norm_sub center position (changed.location 1 : ℂ)
      rw [norm_sub_rev center position] at triangle
      linarith
    · have lower := domain_far_of_block_center_separation (referenceSeparation index same) nearReference (ownReference index patch position inside)
      linarith
  · intro pair member position inside
    have annulus := domains pair.2 position (by simpa only [selectedDipolePatches_outer outer first pair member] using inside)
    have centerIdentity := selectedDipolePatches_center motion 1 outer first pair member
    rw [selectedDipolePatches_outer outer first pair member] at centerIdentity
    rw [centerIdentity] at annulus
    exact annulus
  · rintro ⟨index, patch⟩ outside position inside
    change 4 * length ≤ ‖position - center‖
    by_cases same : index = outer
    · subst index
      have bound := (domains patch position inside).2
      rw [unselectedDipolePatches_center motion 1 outer first patch outside] at bound
      have triangle := norm_sub_le_norm_sub_add_norm_sub center position (selectedDipoleCenter motion 1 outer (!first))
      rw [selectedDipoleCenter_gap, norm_sub_rev center position] at triangle
      linarith
    · have lower := domain_far_of_block_center_separation (alternativeSeparation index same)
        (nearAlternative.trans (by linarith)) (ownAlternative index patch position inside)
      linarith

end EulerNonuniqueness.Paper
