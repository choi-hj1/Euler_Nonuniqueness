import EulerNonuniqueness.Section5.CascadeBlockCenterCoefficientContinuity
import EulerNonuniqueness.Section6.MovingExteriorSeriesContinuity

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_individual_source_series_continuous (scales : Scales)
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
    ∀ radius : ℝ, 0 ≤ radius → radius ≤ scales.location (receiver.val + 1) / (100000 * 96) →
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let blockTerm := fun (power : ℕ) (time : ℝ) =>
      ‖(first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter first.patchMotion current receiver) radius (power + 1) time -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter second.patchMotion current receiver) radius (power + 1) time‖
    let patchTerm := fun (patch : Fin 4) (power : ℕ) (time : ℝ) => (96 : ℝ) ^ (power + 1) *
      ‖(first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid first.patchMotion current receiver patch) radius (power + 1) time -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid second.patchMotion current receiver patch) radius (power + 1) time‖
    (∀ time ∈ Icc 0 path.stop, Summable (fun power : ℕ => blockTerm power time)) ∧
    ContinuousOn (fun time => ∑' power : ℕ, blockTerm power time) (Icc 0 path.stop) ∧
    ∀ patch : Fin 4,
      (∀ time ∈ Icc 0 path.stop, Summable (fun power : ℕ => patchTerm patch power time)) ∧
      ContinuousOn (fun time => ∑' power : ℕ, patchTerm patch power time) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_patch_coefficient_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment clearance patchContinuity radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let distance := changed.location (receiver.val + 1) / 1000
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  change radius ≤ changed.location (receiver.val + 1) / (100000 * 96) at radiusSmall
  have distancePositive : 0 < distance := div_pos (changed.location_pos _) (by norm_num)
  have spacing := changed.location_sum_le_three_distance
    (show receiver.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have normIdeal : ‖ideal‖ = gap := by
    dsimp only [ideal, gap]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have radiusBound : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have physical := (radii (source.val + 1)).le
    have length := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at physical
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at length
    linarith only [physical, length]
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have small96 : (96 : ℝ) * radius / distance < 1 := by
    apply (div_lt_iff₀ distancePositive).mpr
    dsimp only [distance]
    linarith only [radiusSmall, changed.location_pos (receiver.val + 1)]
  have smallOne : (1 : ℝ) * radius / distance < 1 := by
    apply (div_lt_iff₀ distancePositive).mpr
    have weighted := (div_lt_iff₀ distancePositive).mp small96
    linarith only [weighted, radiusNonnegative]
  have sourceMember : source ∈ Finset.univ.erase receiver := Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have oneSideBlock (family : FiniteMovingPatchFamily (count * 4))
      (radiusIdentity : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ label, time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (separated : ∀ time ∈ Icc 0 path.stop, ∀ patch position,
        position ∈ family.patchMotion.domain time source patch → gap / 8 ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖) :
      (∀ time ∈ Icc 0 path.stop, ∀ patch ∈ (Finset.univ : Finset (Fin 4)),
        ∀ position ∈ ((family.quadrupoleSubfamily source).patch patch).domain time,
          distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖) ∧
      ∀ power : ℕ, ContinuousOn ((family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => quadrupoleCenter family.patchMotion current receiver) radius (power + 1)) (Icc 0 path.stop) := by
    have domainGap (time : ℝ) (member : time ∈ Icc 0 path.stop) (patch : Fin 4) (position : ℂ)
        (positionMember : position ∈ ((family.quadrupoleSubfamily source).patch patch).domain time) :
        distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖ := by
      have actual := separated time member patch position positionMember
      dsimp only [distance, gap] at actual ⊢
      linarith only [actual, spacing, changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
    refine ⟨fun time member patch _ position positionMember => domainGap time member patch position positionMember, ?_⟩
    intro power
    apply (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
      Finset.univ (fun current => quadrupoleCenter family.patchMotion current receiver) radius (power + 1)
      (Icc 0 path.stop) distancePositive
      (fun time member => family.quadrupoleCenter_contDiffAt receiver (fun _ => inside time member _))
      (fun time member patch _ => inside time member (finProdFinEquiv (source, patch)))
    intro time member patch _
    have actual := separated time member patch _ ((family.patch (finProdFinEquiv (source, patch))).domain_center_mem time)
    change distance + 3 * (family.patch (finProdFinEquiv (source, patch))).radius ≤
      ‖quadrupoleCenter family.patchMotion time receiver - (family.patch (finProdFinEquiv (source, patch))).center time‖
    rw [radiusIdentity]
    dsimp only [distance, gap] at actual ⊢
    linarith only [actual, spacing, radiusBound, changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have firstBlock := oneSideBlock first (prepared.radiusIdentity source)
    (fun time member _ => globalInside time member)
    (fun time member patch position positionMember =>
      (clearance count phase dipoleAngle prepared path time member receiver).2 source sourceMember patch position positionMember)
  have secondBlock := oneSideBlock second (prepared.referenceWitness.radiusIdentity source)
    (fun time member _ => globalInside time member)
    (fun time member patch position positionMember =>
      (clearance count phase dipoleAngle prepared path time member receiver).1 source sourceMember patch position positionMember)
  have oneSidePatch (family : FiniteMovingPatchFamily (count * 4))
      (radiusIdentity : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (centerIdentity : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        (family.patch (finProdFinEquiv (source, patch))).center time = patchCentroid family.patchMotion time source patch)
      (aligned : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        ‖(patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source) - ideal‖ ≤ 3 * gap / 16)
      (extent : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        ‖patchCentroid family.patchMotion time source patch - quadrupoleCenter family.patchMotion time source‖ ≤
          changed.location (source.val + 1) / 100) :
      ∀ patch time, time ∈ Icc 0 path.stop → ∀ sourcePatch ∈ (Finset.univ : Finset (Fin 4)),
        ∀ position ∈ ((family.quadrupoleSubfamily source).patch sourcePatch).domain time,
          distance ≤ ‖patchCentroid family.patchMotion time receiver patch - position‖ := by
    intro patch time inside sourcePatch _ position positionMember
    have domainBound := (family.patch (finProdFinEquiv (source, sourcePatch))).domain_subset_ball_two_radius time positionMember
    rw [Metric.mem_ball, dist_eq_norm, radiusIdentity, centerIdentity time inside] at domainBound
    have idealTriangle := norm_sub_norm_le ideal
      (patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source)
    rw [normIdeal, norm_sub_rev ideal] at idealTriangle
    have sourceTriangle := norm_sub_le_norm_sub_add_norm_sub position
      (patchCentroid family.patchMotion time source sourcePatch) (quadrupoleCenter family.patchMotion time source)
    have receiverTriangle := norm_sub_le_norm_sub_add_norm_sub
      (patchCentroid family.patchMotion time receiver patch) position (quadrupoleCenter family.patchMotion time source)
    dsimp only [distance, gap] at *
    linarith only [idealTriangle, sourceTriangle, receiverTriangle, domainBound, radiusBound,
      aligned time inside patch, extent time inside sourcePatch, spacing,
      changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have firstPatch := oneSidePatch first (prepared.radiusIdentity source)
    (fun time inside patch => prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) source patch)
    (fun time inside patch => (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).2.1)
    (fun time inside patch => (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.2.2 patch)
  have secondPatch := oneSidePatch second (prepared.referenceWitness.radiusIdentity source)
    (fun time inside patch => prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) source patch)
    (fun time inside patch => (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1)
    (fun time inside patch => (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.2.1 patch)
  have blocks := (first.quadrupoleSubfamily source).continuousOn_weighted_exteriorTaylorCoefficient_difference_tsum
    (second.quadrupoleSubfamily source) Finset.univ Finset.univ
    (fun current => quadrupoleCenter first.patchMotion current receiver)
    (fun current => quadrupoleCenter second.patchMotion current receiver)
    radiusNonnegative distancePositive (by norm_num : (0 : ℝ) ≤ 1) path.stopPositive.le smallOne
    firstBlock.1 secondBlock.1 (fun power => (firstBlock.2 power).sub (secondBlock.2 power))
  simp only [one_pow, one_mul] at blocks
  refine ⟨blocks.1, blocks.2.2, ?_⟩
  intro patch
  have patches := (first.quadrupoleSubfamily source).continuousOn_weighted_exteriorTaylorCoefficient_difference_tsum
    (second.quadrupoleSubfamily source) Finset.univ Finset.univ
    (fun current => patchCentroid first.patchMotion current receiver patch)
    (fun current => patchCentroid second.patchMotion current receiver patch)
    radiusNonnegative distancePositive (by norm_num : (0 : ℝ) ≤ 96) path.stopPositive.le small96
    (firstPatch patch) (secondPatch patch)
    (fun power => patchContinuity count phase dipoleAngle prepared path (receiver, patch) source different radius power)
  exact ⟨patches.1, patches.2.2⟩

end EulerNonuniqueness.Paper
