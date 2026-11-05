import EulerNonuniqueness.Section5.CascadeForeignStrainContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourcePatchCoefficientContinuity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 750000

theorem Scales.eventually_cascade_blockcenter_coefficient_continuous (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver : Fin count, ∀ radius : ℝ, ∀ power : ℕ,
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    ContinuousOn (fun time => first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => quadrupoleCenter first.patchMotion current receiver) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => quadrupoleCenter second.patchMotion current receiver) radius (power + 1) time) (Icc 0 path.stop) ∧
    ContinuousOn (fun time => quadrupoleExteriorCoefficient {scales with frequency := frequency} first.patchMotion receiver time radius power -
      quadrupoleExteriorCoefficient {scales with frequency := frequency} second.patchMotion receiver time radius power) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency clearance radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver radius power
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have radiusSmall (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have first := (radii (source.val + 1)).le
    have second := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at first
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at second
    linarith only [first, second]
  have globalInside (time : ℝ) (member : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [member.1], by linarith only [member.2, path.stopBound]⟩
  have oneSide (family : FiniteMovingPatchFamily (count * 4))
      (densities : ∀ source patch, family.density (finProdFinEquiv (source, patch)) =
        patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4)
      (radiusIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ label, time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (separated : ∀ time ∈ Icc 0 path.stop, ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
        position ∈ family.patchMotion.domain time source patch →
          |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
            ‖quadrupoleCenter family.patchMotion time receiver - position‖) :
      ContinuousOn (family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => quadrupoleCenter family.patchMotion current receiver) radius (power + 1)) (Icc 0 path.stop) ∧
      ContinuousOn (fun time => quadrupoleExteriorCoefficient changed family.patchMotion receiver time radius power) (Icc 0 path.stop) := by
    let distance := changed.location (receiver.val + 1) / 1000
    have positive : 0 < distance := div_pos (changed.location_pos _) (by norm_num)
    have sourceLocations (source : Fin count) (member : source ∈ Finset.univ.erase receiver) :
        changed.location (receiver.val + 1) + changed.location (source.val + 1) ≤
          3 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| :=
      changed.location_sum_le_three_distance (by
        intro identity
        exact (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel identity)).symm)
    have centerGaps (time : ℝ) (member : time ∈ Icc 0 path.stop) (label : Fin (count * 4))
        (foreign : label ∈ foreignQuadrupolePatchLabels receiver) :
        distance + 3 * (family.patch label).radius ≤
          ‖quadrupoleCenter family.patchMotion time receiver - (family.patch label).center time‖ := by
      obtain ⟨⟨source, patch⟩, rfl⟩ := finProdFinEquiv.surjective label
      have sourceMember := Finset.mem_erase.mpr
        ⟨(mem_foreignQuadrupolePatchLabels receiver source patch).mp foreign, Finset.mem_univ source⟩
      have actual := separated time member source sourceMember patch _
        ((family.patch (finProdFinEquiv (source, patch))).domain_center_mem time)
      rw [radiusIdentity]
      dsimp only [distance]
      linarith only [actual, sourceLocations source sourceMember, radiusSmall source,
        changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
    have regular := family.exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
      (foreignQuadrupolePatchLabels receiver) (fun current => quadrupoleCenter family.patchMotion current receiver)
      radius (power + 1) (Icc 0 path.stop) positive
      (fun time member => family.quadrupoleCenter_contDiffAt receiver (fun _ => inside time member _))
      (fun time member label _ => inside time member label) centerGaps
    refine ⟨regular, regular.congr ?_⟩
    intro time member
    apply (family.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient changed densities receiver radius time power positive ?_).symm
    intro source sourceMember patch position positionMember
    have actual := separated time member source sourceMember patch position positionMember
    dsimp only [distance]
    linarith only [actual, sourceLocations source sourceMember, changed.location_pos (receiver.val + 1),
      changed.location_pos (source.val + 1)]
  have clear (time : ℝ) (inside : time ∈ Icc 0 path.stop) := clearance count phase dipoleAngle prepared path time inside receiver
  have first := oneSide prepared.trajectory.movingFamily prepared.densityIdentity prepared.radiusIdentity
    (fun time member _ => globalInside time member) (fun time member => (clear time member).2)
  have second := oneSide prepared.referenceWitness.trajectory.movingFamily prepared.referenceWitness.densityIdentity
    prepared.referenceWitness.radiusIdentity (fun time member _ => globalInside time member)
    (fun time member => (clear time member).1)
  exact ⟨first.1.sub second.1, first.2.sub second.2⟩

end EulerNonuniqueness.Paper
