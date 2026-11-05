import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.ForeignStrainRegularity
import EulerNonuniqueness.Section6.MovingForeignCoefficientSum
import EulerNonuniqueness.Section4.ReferenceForeignStrainIdentity
import EulerNonuniqueness.Section6.PaperRelativeShapeForcingSplit

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.externalShapeStrain_continuousOn_of_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (index : Fin count)
    (times : Set ℝ) {distance : ℝ} (distancePositive : 0 < distance)
    (density : ∀ source patch, family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (inside : ∀ time ∈ times, ∀ source,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (gaps : ∀ time ∈ times, ∀ source ∈ foreignQuadrupolePatchLabels index,
      distance + 3 * (family.patch source).radius ≤
        ‖quadrupoleCenter family.patchMotion time index - (family.patch source).center time‖) :
    ContinuousOn (fun time => quadrupoleExternalShapeStrain scales family.patchMotion time index) times := by
  have regular : ContinuousOn (family.foreignQuadrupoleStrain index) times := fun time member =>
    (family.foreignQuadrupoleStrain_contDiffAt index (inside time member) distancePositive
      (gaps time member)).continuousAt.continuousWithinAt
  apply regular.congr
  intro time member
  have separated : ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖quadrupoleCenter family.patchMotion time index - position‖ := by
    intro source sourceMember position positionMember
    have bounded : ‖position - (family.patch source).center time‖ < 2 * (family.patch source).radius := by
      simpa only [Metric.mem_ball, dist_eq_norm] using
        (family.patch source).domain_subset_ball_two_radius time positionMember
    have triangle := norm_add_le (quadrupoleCenter family.patchMotion time index - position)
      (position - (family.patch source).center time)
    rw [sub_add_sub_cancel] at triangle
    linarith [gaps time member source sourceMember, (family.patch source).radius_positive]
  have coefficients := family.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient
    scales density index 1 time 0 distancePositive
    (fun source sourceMember patch position positionMember => separated (finProdFinEquiv (source, patch))
      ((mem_foreignQuadrupolePatchLabels index source patch).mpr (Finset.mem_erase.mp sourceMember).1)
      position positionMember)
  change quadrupoleExternalShapeStrain scales family.patchMotion time index = family.foreignQuadrupoleStrain index time
  rw [show family.foreignQuadrupoleStrain index time =
      quadrupoleExteriorCoefficient scales family.patchMotion index time 1 0 from coefficients]
  exact (Section6.exteriorVorticityCoefficient_zero_eq_complexStrain _ _ _).symm

theorem Scales.eventually_cascade_foreign_strain_continuous (scales : Scales)
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
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
      ContinuousOn (fun time => quadrupoleExternalShapeStrain {scales with frequency := frequency}
        prepared.trajectory.movingFamily.patchMotion time index) (Icc 0 path.stop) ∧
      ContinuousOn (fun time => quadrupoleExternalShapeStrain {scales with frequency := frequency}
        prepared.reference time index) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency clearance radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path index
  let changed : Scales := {scales with frequency := frequency}
  have radiusSmall (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have first := (radii (source.val + 1)).le
    have second := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at first
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at second
    linarith
  have globalInside (time : ℝ) (member : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩
  have oneFamily (family : FiniteMovingPatchFamily (count * 4))
      (density : ∀ source patch, family.density (finProdFinEquiv (source, patch)) =
        patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4)
      (radius : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ source,
        time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
      (separated : ∀ time ∈ Icc 0 path.stop, ∀ source ∈ Finset.univ.erase index, ∀ patch position,
        position ∈ family.patchMotion.domain time source patch →
          |changed.location (index.val + 1) - changed.location (source.val + 1)| / 8 ≤
            ‖quadrupoleCenter family.patchMotion time index - position‖) :
      ContinuousOn (fun time => quadrupoleExternalShapeStrain changed family.patchMotion time index) (Icc 0 path.stop) := by
    apply family.externalShapeStrain_continuousOn_of_center_gaps changed index _
      (div_pos (changed.location_pos (index.val + 1)) (by norm_num : (0 : ℝ) < 1000)) density inside
    intro time member label labelMember
    obtain ⟨⟨source, patch⟩, rfl⟩ := (finProdFinEquiv : Fin count × Fin 4 ≃ Fin (count * 4)).surjective label
    have different := (mem_foreignQuadrupolePatchLabels index source patch).mp labelMember
    have actual := separated time member source (Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩) patch _
      ((family.patch (finProdFinEquiv (source, patch))).domain_center_mem time)
    have locations := changed.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)).symm)
    rw [radius]
    linarith [radiusSmall source, changed.location_pos (index.val + 1), changed.location_pos (source.val + 1)]
  have clear (time : ℝ) (member : time ∈ Icc 0 path.stop) := clearance count phase dipoleAngle prepared path time member index
  constructor
  · exact oneFamily prepared.trajectory.movingFamily prepared.densityIdentity prepared.radiusIdentity
      (fun time member _ => globalInside time member) (fun time member => (clear time member).2)
  · have actual := oneFamily prepared.referenceWitness.trajectory.movingFamily prepared.referenceWitness.densityIdentity
      prepared.referenceWitness.radiusIdentity (fun time member _ => globalInside time member)
      (fun time member => (clear time member).1)
    simpa only [prepared.referenceIdentity] using actual

end EulerNonuniqueness.Paper
