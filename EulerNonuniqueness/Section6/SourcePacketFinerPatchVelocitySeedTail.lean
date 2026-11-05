import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment
import EulerNonuniqueness.Section6.MovingQuadrupoleFieldBounds
import EulerNonuniqueness.Section1.FinerCirculationSeedTail
import EulerNonuniqueness.Section3.FinitePatchRestriction

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem Scales.eventually_actual_finer_patch_velocity_seed_tail (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count × Fin 4,
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    (∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.1.val + 2 ≤ source.val),
      ‖biotSavart (quadrupoleDensity changed alternative time source) (patchCentroid alternative time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity changed reference time source) (patchCentroid reference time receiver.1 receiver.2)‖) /
        changed.location (receiver.1.val + 1) ≤ tolerance * changed.seed (receiver.1.val + 1) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_finer_circulation_seed_tail ratioBound alphaPositive ratioPower 1 1
      (tolerance := tolerance * Real.pi / 96) (by positivity),
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment tail frequencyOne radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  rw [prepared.referenceIdentity]
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let selected := Finset.univ.filter (fun source : Fin count => receiver.1.val + 2 ≤ source.val)
  let term := fun index : ℕ => changed.circulation (receiver.1.val + 3 + index) /
    changed.location (receiver.1.val + 3 + index)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have referenceEvolution : FinitePatchEvolution changed first path.stop :=
    prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])
  have radiusSmall (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have radiusLength : changed.radius (source.val + 1) ≤ changed.length (source.val + 1) := by
      simpa only [one_mul] using (radii (source.val + 1)).le
    exact radiusLength.trans (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (source.val + 1)).le)
  have inverseReceiver : 1 / changed.location (receiver.1.val + 1) ≤ changed.omega (receiver.1.val + 2) := by
    have firstPower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound (receiver.1.val + 1)
    have grow : changed.ratio ^ (receiver.1.val + 1) ≤ changed.ratio ^ (receiver.1.val + 2) := by
      calc
        _ ≤ changed.ratio ^ (receiver.1.val + 1) * changed.ratio :=
          le_mul_of_one_le_right (pow_nonneg ratioPositive.le _) (by change 1 ≤ scales.ratio; linarith only [ratioBound])
        _ = _ := (pow_succ changed.ratio (receiver.1.val + 1)).symm
    calc
      _ = (2 : ℝ) ^ (receiver.1.val + 1) := by rw [one_div, changed.location_eq_inv_pow, inv_inv]
      _ ≤ changed.ratio ^ (receiver.1.val + 2) := firstPower.trans grow
      _ ≤ changed.frequency * changed.ratio ^ (receiver.1.val + 2) :=
        le_mul_of_one_le_left (pow_nonneg ratioPositive.le _) frequencyOne
      _ = _ := rfl
  have termNonnegative (index : ℕ) : 0 ≤ term index :=
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (changed.location_pos _).le
  have termSummable : Summable term := by
    have shifted := (changed.circulation_location_summable frequencyOne ratioBound alphaPositive 1).comp_injective
      (show Function.Injective (fun index : ℕ => receiver.1.val + 2 + index) from
        fun _ _ equality => Nat.add_left_cancel equality)
    simpa only [pow_one, term, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using shifted
  have tailInjective : Set.InjOn (fun source : Fin count => source.val - (receiver.1.val + 2)) selected := by
    intro left leftMember right rightMember equality
    have leftBound := (Finset.mem_filter.mp leftMember).2
    have rightBound := (Finset.mem_filter.mp rightMember).2
    dsimp only at equality
    apply Fin.ext
    omega
  have finiteTail : (∑ source ∈ selected, term (source.val - (receiver.1.val + 2))) ≤ ∑' index, term index := by
    rw [← Finset.sum_image tailInjective]
    exact termSummable.sum_le_tsum _ (fun index _ => termNonnegative index)
  have scalarTail : changed.omega (receiver.1.val + 2) * (∑' index, term index) ≤
      tolerance * Real.pi / 96 * changed.seed (receiver.1.val + 1) := by
    simpa only [pow_one, term, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tail (receiver.1.val + 1)
  have individual (source : Fin count) (member : source ∈ selected) :
      ‖biotSavart (quadrupoleDensity changed second time source) (patchCentroid second time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity changed first time source) (patchCentroid first time receiver.1 receiver.2)‖ /
          changed.location (receiver.1.val + 1) ≤
        (96 / Real.pi) * changed.omega (receiver.1.val + 2) * term (source.val - (receiver.1.val + 2)) := by
    have finer := (Finset.mem_filter.mp member).2
    have different : receiver.1 ≠ source := by intro same; subst source; omega
    have differentIndices : receiver.1.val + 1 ≠ source.val + 1 :=
      fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    let gap := |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)|
    let ideal : ℂ := (changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    have gapPositive : 0 < gap := changed.location_distance_pos differentIndices
    have sourcePositive := changed.location_pos (source.val + 1)
    have receiverPositive := changed.location_pos (receiver.1.val + 1)
    have spacing := changed.location_sum_le_three_distance differentIndices
    have normIdeal : ‖ideal‖ = gap := by
      dsimp only [ideal, gap]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have geometry := alignment count phase dipoleAngle prepared path time inside receiver source different
    have supportGap (motion : PatchMotion count)
        (aligned : ‖(patchCentroid motion time receiver.1 receiver.2 - quadrupoleCenter motion time source) - ideal‖ ≤ 3 * gap / 16)
        (extent : ∀ patch, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
          changed.location (source.val + 1) / 100)
        (domains : ∀ patch position, position ∈ motion.domain time source patch →
          ‖position - patchCentroid motion time source patch‖ ≤ 2 * changed.radius (source.val + 1)) :
        ∀ patch position, position ∈ motion.domain time source patch →
          gap / 8 ≤ ‖patchCentroid motion time receiver.1 receiver.2 - position‖ := by
      intro patch position inDomain
      have firstTriangle := norm_sub_le_norm_sub_add_norm_sub ideal
        (patchCentroid motion time receiver.1 receiver.2 - quadrupoleCenter motion time source) 0
      rw [sub_zero, sub_zero, norm_sub_rev ideal _, normIdeal] at firstTriangle
      have secondTriangle := norm_sub_le_norm_sub_add_norm_sub
        (patchCentroid motion time receiver.1 receiver.2) position (quadrupoleCenter motion time source)
      have thirdTriangle := norm_sub_le_norm_sub_add_norm_sub position
        (patchCentroid motion time source patch) (quadrupoleCenter motion time source)
      linarith only [firstTriangle, secondTriangle, thirdTriangle, aligned, extent patch,
        domains patch position inDomain, radiusSmall source, spacing, receiverPositive, gapPositive]
    have firstSeparated := supportGap first geometry.1 geometry.2.2.1 (fun patch position inDomain => by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using
        prepared.referenceWitness.trajectory.domain_subset_centroid_ball changed prepared.referenceWitness.radiusIdentity
          (fun _ => rfl) globalInside source patch inDomain)
    have secondSeparated := supportGap second geometry.2.1 geometry.2.2.2 (fun patch position inDomain => by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using
        prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity
          (fun _ => rfl) globalInside source patch inDomain)
    have firstBound := (referenceEvolution.quadrupole_biotSavart_bounds_from_material_geometry inside amplitudePositive
      frequencyPositive ratioPositive source (div_pos gapPositive (by norm_num)) firstSeparated firstSeparated).1
    have secondBound := (path.evolution.quadrupole_biotSavart_bounds_from_material_geometry inside amplitudePositive
      frequencyPositive ratioPositive source (div_pos gapPositive (by norm_num)) secondSeparated secondSeparated).1
    have coarse : ‖biotSavart (quadrupoleDensity changed second time source) (patchCentroid second time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity changed first time source) (patchCentroid first time receiver.1 receiver.2)‖ ≤
        32 * changed.circulation (source.val + 1) / (Real.pi * gap) := by
      exact (norm_sub_le _ _).trans ((add_le_add secondBound firstBound).trans_eq (by ring))
    have inverseGap : 1 / gap ≤ 3 / changed.location (source.val + 1) := by
      apply (div_le_div_iff₀ gapPositive sourcePositive).mpr
      linarith only [spacing, receiverPositive]
    have circulationNonnegative := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have sourceBound : 32 * changed.circulation (source.val + 1) / (Real.pi * gap) ≤
        (96 / Real.pi) * (changed.circulation (source.val + 1) / changed.location (source.val + 1)) := by
      have actual := mul_le_mul_of_nonneg_left inverseGap
        (show 0 ≤ 32 * changed.circulation (source.val + 1) / Real.pi by positivity)
      convert actual using 1 <;> ring
    have divided := div_le_div_of_nonneg_right (coarse.trans sourceBound) receiverPositive.le
    have receiverBound := mul_le_mul_of_nonneg_left inverseReceiver
      (show 0 ≤ (96 / Real.pi) * (changed.circulation (source.val + 1) / changed.location (source.val + 1)) by positivity)
    have indexIdentity : receiver.1.val + 3 + (source.val - (receiver.1.val + 2)) = source.val + 1 := by omega
    dsimp only [term]
    rw [indexIdentity]
    apply divided.trans
    convert receiverBound using 1 <;> ring
  have finiteBound := Finset.sum_le_sum individual
  rw [← Finset.sum_div, ← Finset.mul_sum] at finiteBound
  have weightedFinite := mul_le_mul_of_nonneg_left finiteTail
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 96 / Real.pi)
      (changed.omega_pos frequencyPositive ratioPositive (receiver.1.val + 2)).le)
  have weightedTail := mul_le_mul_of_nonneg_left scalarTail (show (0 : ℝ) ≤ 96 / Real.pi by positivity)
  calc
    _ ≤ (96 / Real.pi) * changed.omega (receiver.1.val + 2) * (∑' index, term index) := finiteBound.trans weightedFinite
    _ ≤ (96 / Real.pi) * (tolerance * Real.pi / 96 * changed.seed (receiver.1.val + 1)) := by
      simpa only [mul_assoc] using weightedTail
    _ = _ := by field_simp; ring

end EulerNonuniqueness.Paper
