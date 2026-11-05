import EulerNonuniqueness.Section5.CascadeForeignStrainContinuity
import EulerNonuniqueness.Section6.MovingSelectedStrainRegularity
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem FiniteMovingPatchFamily.quadrupoleComplexStrain_continuousOn_of_center_gaps
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (receiver source : Fin count) (times : Set ℝ) {distance : ℝ} (distancePositive : 0 < distance)
    (density : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (inside : ∀ time ∈ times, ∀ label, time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
    (centerGaps : ∀ time ∈ times, ∀ patch : Fin 4,
      distance + 3 * (family.patch (finProdFinEquiv (source, patch))).radius ≤
        ‖quadrupoleCenter family.patchMotion time receiver - (family.patch (finProdFinEquiv (source, patch))).center time‖) :
    ContinuousOn (fun time => vorticityComplexStrain (quadrupoleDensity scales family.patchMotion time source)
      (quadrupoleCenter family.patchMotion time receiver)) times := by
  let center := fun time => quadrupoleCenter family.patchMotion time receiver
  have regular := (family.quadrupoleSubfamily source).subfamilyComplexStrain_continuousOn_of_center_gaps
    Finset.univ center times distancePositive
    (fun time member => family.quadrupoleCenter_contDiffAt receiver (fun _ => inside time member _))
    (fun time member patch _ => inside time member (finProdFinEquiv (source, patch)))
    (fun time member patch _ => centerGaps time member patch)
  have same (time : ℝ) : (family.quadrupoleSubfamily source).subfamilyVorticity Finset.univ time =
      quadrupoleDensity scales family.patchMotion time source := by
    funext position
    apply Finset.sum_congr rfl
    intro patch _
    change ((family.patch (finProdFinEquiv (source, patch))).domain time).indicator
      (fun _ => family.density (finProdFinEquiv (source, patch))) position = _
    rw [density]
    rfl
  apply regular.congr
  intro time _
  exact (congrArg (fun vorticity => vorticityComplexStrain vorticity (center time)) (same time)).symm

theorem Scales.eventually_cascade_individual_source_strain_continuous (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source →
      let changed : Scales := {scales with frequency := frequency}
      ContinuousOn (fun time => vorticityComplexStrain
        (quadrupoleDensity changed prepared.trajectory.movingFamily.patchMotion time source)
        (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver)) (Icc 0 path.stop) ∧
      ContinuousOn (fun time => vorticityComplexStrain (quadrupoleDensity changed prepared.reference time source)
        (quadrupoleCenter prepared.reference time receiver)) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency clearance radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have sourceMember : source ∈ Finset.univ.erase receiver := Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have radiusSmall : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have first := (radii (source.val + 1)).le
    have second := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at first
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at second
    linarith
  have globalInside (time : ℝ) (member : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩
  have oneFamily (family : FiniteMovingPatchFamily (count * 4))
      (density : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4)
      (radius : ∀ index patch, (family.patch (finProdFinEquiv (index, patch))).radius = changed.radius (index.val + 1))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ label, time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (separated : ∀ time ∈ Icc 0 path.stop, ∀ patch position,
        position ∈ family.patchMotion.domain time source patch →
          |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
            ‖quadrupoleCenter family.patchMotion time receiver - position‖) :
      ContinuousOn (fun time => vorticityComplexStrain (quadrupoleDensity changed family.patchMotion time source)
        (quadrupoleCenter family.patchMotion time receiver)) (Icc 0 path.stop) := by
    apply family.quadrupoleComplexStrain_continuousOn_of_center_gaps changed receiver source _
      (div_pos (changed.location_pos (receiver.val + 1)) (by norm_num : (0 : ℝ) < 1000)) density inside
    intro time member patch
    have actual := separated time member patch _
      ((family.patch (finProdFinEquiv (source, patch))).domain_center_mem time)
    have spacing := changed.location_sum_le_three_distance
      (show receiver.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
    rw [radius]
    linarith [radiusSmall, changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have clear (time : ℝ) (member : time ∈ Icc 0 path.stop) := clearance count phase dipoleAngle prepared path time member receiver
  constructor
  · exact oneFamily prepared.trajectory.movingFamily prepared.densityIdentity prepared.radiusIdentity
      (fun time member _ => globalInside time member) (fun time member => (clear time member).2 source sourceMember)
  · have actual := oneFamily prepared.referenceWitness.trajectory.movingFamily prepared.referenceWitness.densityIdentity
      prepared.referenceWitness.radiusIdentity (fun time member _ => globalInside time member)
      (fun time member => (clear time member).1 source sourceMember)
    simpa only [prepared.referenceIdentity] using actual

end EulerNonuniqueness.Paper
