import EulerNonuniqueness.Section5.CascadeBlockCenterCoefficientContinuity
import EulerNonuniqueness.Section6.MovingExteriorSeriesContinuity

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_foreign_coefficient_series_continuous (scales : Scales)
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
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver : Fin count, ∀ radius : ℝ, 0 ≤ radius →
    radius ≤ scales.location (receiver.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let patchCoefficient := fun (patch : Fin 4) (power : ℕ) (time : ℝ) =>
      first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid first.patchMotion current receiver patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid second.patchMotion current receiver patch) radius (power + 1) time
    let blockCoefficient := fun (power : ℕ) (time : ℝ) =>
      quadrupoleExteriorCoefficient changed first.patchMotion receiver time radius power -
        quadrupoleExteriorCoefficient changed second.patchMotion receiver time radius power
    (∀ patch : Fin 4,
      (∀ time ∈ Icc 0 path.stop, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖patchCoefficient patch power time‖)) ∧
      ContinuousOn (fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖patchCoefficient patch power time‖) (Icc 0 path.stop)) ∧
    (∀ time ∈ Icc 0 path.stop, Summable (fun power : ℕ => ‖blockCoefficient power time‖)) ∧
    ContinuousOn (fun time => ∑' power : ℕ, ‖blockCoefficient power time‖) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_patch_coefficient_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_blockcenter_coefficient_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment clearance patchContinuity blockContinuity radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let distance := changed.location (receiver.val + 1) / 1000
  have distancePositive : 0 < distance := div_pos (changed.location_pos _) (by norm_num)
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have radiusBound (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have firstBound := (radii (source.val + 1)).le
    have secondBound := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at firstBound
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at secondBound
    linarith only [firstBound, secondBound]
  have small96 : (96 : ℝ) * radius / distance < 1 := by
    apply (div_lt_iff₀ distancePositive).mpr
    change radius ≤ changed.location (receiver.val + 1) / (100000 * 96) at radiusSmall
    dsimp only [distance]
    linarith only [radiusSmall, changed.location_pos (receiver.val + 1)]
  have smallOne : (1 : ℝ) * radius / distance < 1 := by
    apply (div_lt_iff₀ distancePositive).mpr
    have actual := (div_lt_iff₀ distancePositive).mp small96
    linarith only [actual, radiusNonnegative]
  have oneSidePatch (family : FiniteMovingPatchFamily (count * 4))
      (radiusIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (centerIdentity : ∀ time ∈ Icc 0 path.stop, ∀ source patch,
        (family.patch (finProdFinEquiv (source, patch))).center time = patchCentroid family.patchMotion time source patch)
      (aligned : ∀ time ∈ Icc 0 path.stop, ∀ patch source, receiver ≠ source →
        ‖(patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source) -
          ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))‖ ≤
            3 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 16)
      (extent : ∀ time ∈ Icc 0 path.stop, ∀ source, receiver ≠ source → ∀ patch,
        ‖patchCentroid family.patchMotion time source patch - quadrupoleCenter family.patchMotion time source‖ ≤
          changed.location (source.val + 1) / 100) :
      ∀ patch time, time ∈ Icc 0 path.stop → ∀ label ∈ foreignQuadrupolePatchLabels receiver,
        ∀ position ∈ (family.patch label).domain time,
          distance ≤ ‖patchCentroid family.patchMotion time receiver patch - position‖ := by
    intro patch time inside label foreign position positionMember
    obtain ⟨⟨source, sourcePatch⟩, rfl⟩ := finProdFinEquiv.surjective label
    have different : receiver ≠ source := ((mem_foreignQuadrupolePatchLabels receiver source sourcePatch).mp foreign).symm
    have spacing := changed.location_sum_le_three_distance
      (show receiver.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
    have domainBound := (family.patch (finProdFinEquiv (source, sourcePatch))).domain_subset_ball_two_radius time positionMember
    rw [Metric.mem_ball, dist_eq_norm, radiusIdentity, centerIdentity time inside] at domainBound
    have normIdeal : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ =
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have idealTriangle := norm_sub_norm_le
      ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))
      (patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source)
    rw [normIdeal, norm_sub_rev ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))] at idealTriangle
    have sourceTriangle := norm_sub_le_norm_sub_add_norm_sub position
      (patchCentroid family.patchMotion time source sourcePatch) (quadrupoleCenter family.patchMotion time source)
    have receiverTriangle := norm_sub_le_norm_sub_add_norm_sub
      (patchCentroid family.patchMotion time receiver patch) position (quadrupoleCenter family.patchMotion time source)
    dsimp only [distance]
    linarith only [idealTriangle, sourceTriangle, receiverTriangle, domainBound, radiusBound source,
      aligned time inside patch source different, extent time inside source different sourcePatch, spacing,
      changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have firstPatchClearance := oneSidePatch first prepared.radiusIdentity
    (fun time inside source patch => prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) source patch)
    (fun time inside patch source different => (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).2.1)
    (fun time inside source different => (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.2.2)
  have secondPatchClearance := oneSidePatch second prepared.referenceWitness.radiusIdentity
    (fun time inside source patch => prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) source patch)
    (fun time inside patch source different => (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1)
    (fun time inside source different => (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.2.1)
  have oneSideBlock (family : FiniteMovingPatchFamily (count * 4))
      (separated : ∀ time ∈ Icc 0 path.stop, ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
        position ∈ family.patchMotion.domain time source patch →
          |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
            ‖quadrupoleCenter family.patchMotion time receiver - position‖) :
      ∀ time ∈ Icc 0 path.stop, ∀ label ∈ foreignQuadrupolePatchLabels receiver,
        ∀ position ∈ (family.patch label).domain time,
          distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖ := by
    intro time inside label foreign position positionMember
    obtain ⟨⟨source, patch⟩, rfl⟩ := finProdFinEquiv.surjective label
    have member := Finset.mem_erase.mpr
      ⟨(mem_foreignQuadrupolePatchLabels receiver source patch).mp foreign, Finset.mem_univ source⟩
    have actual := separated time inside source member patch position positionMember
    have spacing := changed.location_sum_le_three_distance (show receiver.val + 1 ≠ source.val + 1 by
      intro identity
      exact (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel identity)).symm)
    dsimp only [distance]
    linarith only [actual, spacing, changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have firstBlockClearance := oneSideBlock first
    (fun time inside => (clearance count phase dipoleAngle prepared path time inside receiver).2)
  have secondBlockClearance := oneSideBlock second
    (fun time inside => (clearance count phase dipoleAngle prepared path time inside receiver).1)
  have patchCoefficientContinuous (patch : Fin 4) (power : ℕ) : ContinuousOn (fun time =>
      first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid first.patchMotion current receiver patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid second.patchMotion current receiver patch) radius (power + 1) time) (Icc 0 path.stop) := by
    have identity : (fun time => first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid first.patchMotion current receiver patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid second.patchMotion current receiver patch) radius (power + 1) time) =
        fun time => ∑ source ∈ Finset.univ.erase receiver,
          ((first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
              (fun current => patchCentroid first.patchMotion current receiver patch) radius (power + 1) time -
            (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
              (fun current => patchCentroid second.patchMotion current receiver patch) radius (power + 1) time) := by
      funext time
      rw [first.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
        second.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, Finset.sum_sub_distrib]
    rw [identity]
    apply continuousOn_finset_sum
    intro source member
    exact patchContinuity count phase dipoleAngle prepared path (receiver, patch) source
      (Ne.symm (Finset.mem_erase.mp member).1) radius power
  have blockIdentity (family : FiniteMovingPatchFamily (count * 4))
      (densities : ∀ source patch, family.density (finProdFinEquiv (source, patch)) =
        patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4)
      (separated : ∀ time ∈ Icc 0 path.stop, ∀ label ∈ foreignQuadrupolePatchLabels receiver,
        ∀ position ∈ (family.patch label).domain time,
          distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖)
      (power : ℕ) (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => quadrupoleCenter family.patchMotion current receiver) radius (power + 1) time =
        quadrupoleExteriorCoefficient changed family.patchMotion receiver time radius power := by
    apply family.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient changed densities receiver radius time power distancePositive
    intro source member patch position positionMember
    exact separated time inside (finProdFinEquiv (source, patch))
      ((mem_foreignQuadrupolePatchLabels receiver source patch).mpr (Finset.mem_erase.mp member).1) position positionMember
  have blocks := first.continuousOn_weighted_exteriorTaylorCoefficient_difference_tsum second
    (foreignQuadrupolePatchLabels receiver) (foreignQuadrupolePatchLabels receiver)
    (fun current => quadrupoleCenter first.patchMotion current receiver)
    (fun current => quadrupoleCenter second.patchMotion current receiver)
    radiusNonnegative distancePositive (by norm_num : (0 : ℝ) ≤ 1) path.stopPositive.le smallOne
    firstBlockClearance secondBlockClearance
    (fun power => (blockContinuity count phase dipoleAngle prepared path receiver radius power).1)
  simp only [one_pow, one_mul] at blocks
  refine ⟨?_, ?_, ?_⟩
  · intro patch
    have patches := first.continuousOn_weighted_exteriorTaylorCoefficient_difference_tsum second
      (foreignQuadrupolePatchLabels receiver) (foreignQuadrupolePatchLabels receiver)
      (fun current => patchCentroid first.patchMotion current receiver patch)
      (fun current => patchCentroid second.patchMotion current receiver patch)
      radiusNonnegative distancePositive (by norm_num : (0 : ℝ) ≤ 96) path.stopPositive.le small96
      (firstPatchClearance patch) (secondPatchClearance patch) (patchCoefficientContinuous patch)
    exact ⟨patches.1, patches.2.2⟩
  · intro time inside
    exact (blocks.1 time inside).congr (fun power => by
      rw [blockIdentity first prepared.densityIdentity firstBlockClearance power time inside,
        blockIdentity second prepared.referenceWitness.densityIdentity secondBlockClearance power time inside])
  · apply blocks.2.2.congr
    intro time inside
    apply tsum_congr
    intro power
    rw [blockIdentity first prepared.densityIdentity firstBlockClearance power time inside,
      blockIdentity second prepared.referenceWitness.densityIdentity secondBlockClearance power time inside]

end EulerNonuniqueness.Paper
