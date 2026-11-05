import EulerNonuniqueness.Section5.CascadeReferenceForeignCoefficientNorm
import EulerNonuniqueness.Section5.CascadeSourcePreparedPair

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem foreign_patch_absolute_side_at_radius
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time factor radius : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyOne : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (factorPositive : 0 < factor) (receiver : Fin count × Fin 4)
    (centerIdentity : (family.patch (finProdFinEquiv receiver)).center time =
      patchCentroid family.patchMotion time receiver.1 receiver.2)
    (centerGaps : ∀ source : Fin count × Fin 4, receiver ≠ source →
      2 * (family.patch (finProdFinEquiv source)).radius +
        (factor / 8) * scales.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) ≤
        ‖(family.patch (finProdFinEquiv receiver)).center time - (family.patch (finProdFinEquiv source)).center time‖)
    (domainGaps : ∀ source ∈ foreignQuadrupolePatchLabels receiver.1,
      ∀ position ∈ (family.patch source).domain time,
        factor / 1600 * scales.location (receiver.1.val + 1) ≤
          ‖(family.patch (finProdFinEquiv receiver)).center time - position‖)
    (radiusNonnegative : 0 ≤ radius)
    (radiusSmall : 96 * radius / (factor / 1600 * scales.location (receiver.1.val + 1)) ≤ 1 / 2) :
    let selected := foreignQuadrupolePatchLabels receiver.1
    let center := fun current => patchCentroid family.patchMotion current receiver.1 receiver.2
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖) ∧
    (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖) ≤
        96 / Real.pi * (2304 * scales.strain / (factor / 8) ^ 2) := by
  let selected := foreignQuadrupolePatchLabels receiver.1
  let center := fun current => patchCentroid family.patchMotion current receiver.1 receiver.2
  let distance := factor / 1600 * scales.location (receiver.1.val + 1)
  have distancePositive : 0 < distance := by
    dsimp only [distance]
    exact mul_pos (div_pos factorPositive (by norm_num)) (scales.location_pos _)
  have separated (source : Fin (count * 4)) (member : source ∈ selected)
      (position : ℂ) (sourceInside : position ∈ (family.patch source).domain time) : distance ≤ ‖center time - position‖ := by
    dsimp only [center]
    rw [← centerIdentity]
    exact domainGaps source member position sourceInside
  have scaledSeparated (label : Fin (count * 4)) (member : label ∈ selected)
      (position : ℂ) (sourceInside : position ∈ (family.patch label).domain time) :
      (factor / 8) * (|scales.location (receiver.1.val + 1) -
        scales.location ((finProdFinEquiv.symm label).1.val + 1)| / 8) ≤ ‖center time - position‖ := by
    let source := finProdFinEquiv.symm label
    have sourceIdentity : finProdFinEquiv source = label := finProdFinEquiv.apply_symm_apply label
    have sourceDifferent : source.1 ≠ receiver.1 := by
      apply (mem_foreignQuadrupolePatchLabels receiver.1 source.1 source.2).mp
      simpa only [sourceIdentity] using member
    have different : receiver ≠ source := fun equality => sourceDifferent (congrArg Prod.fst equality.symm)
    have indexDifferent : source.1.val + 1 ≠ receiver.1.val + 1 :=
      fun equality => sourceDifferent (Fin.ext (Nat.add_right_cancel equality))
    have lower := centerGaps source different
    rw [Scales.individualInteractionDistance, if_neg indexDifferent, sourceIdentity] at lower
    have sourceBound := (Metric.mem_ball.mp ((family.patch label).domain_subset_ball time sourceInside)).le
    rw [dist_eq_norm] at sourceBound
    have triangle := norm_add_le ((family.patch (finProdFinEquiv receiver)).center time - position)
      (position - (family.patch label).center time)
    rw [sub_add_sub_cancel] at triangle
    dsimp only [center]
    rw [← centerIdentity]
    linarith only [lower, sourceBound, triangle]
  have massBound := family.external_inverseSquare_weight_le_scaled_strain scales evolution inside densityIdentity
    amplitudePositive frequencyOne ratioBound alphaPositive (show 0 < factor / 8 by positivity)
    receiver.1 (center time) scaledSeparated
  have summable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖) := by
    simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ distancePositive separated]
    exact Section6.summable_exteriorVorticityCoefficient_weight (family.subfamilyVorticity_integrable selected time)
      (center time) radiusNonnegative distancePositive (by norm_num)
      (family.subfamily_support_separated selected (center time) time distance separated)
      (radiusSmall.trans_lt (by norm_num))
  have actual := family.tsum_exteriorTaylorCoefficient_weight_le selected center radius time radiusNonnegative distancePositive
    (by norm_num : (0 : ℝ) ≤ 96) separated radiusSmall
  exact ⟨summable, actual.trans (mul_le_mul_of_nonneg_left massBound (by positivity : (0 : ℝ) ≤ 96 / Real.pi))⟩

theorem exists_uniform_actual_foreign_patch_absolute_coefficient_bound :
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 → ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {threshold referenceConstant : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ phase dipoleAngle : ℕ → ℝ, ∀ {rawCap scaleRoot shapeRadius monitor boundaryConstant : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ time ∈ Icc 0 path.stop,
    ∀ radius : ℝ, 0 ≤ radius → radius ≤ factor / 39321600 * scales.location (index.val + 1) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let selected := foreignQuadrupolePatchLabels index
    let firstCoefficient := fun (patch : Fin 4) (power : ℕ) => first.exteriorTaylorCoefficient selected
      (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time
    let secondCoefficient := fun (patch : Fin 4) (power : ℕ) => second.exteriorTaylorCoefficient selected
      (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time
    let bound := 96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2)
    (∀ patch : Fin 4,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power‖) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖secondCoefficient patch power‖) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power - secondCoefficient patch power‖) ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power‖) ≤ bound ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖secondCoefficient patch power‖) ≤ bound ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power - secondCoefficient patch power‖) ≤ 2 * bound) ∧
    (∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖firstCoefficient patch power - secondCoefficient patch power‖) ≤ constant * changed.strain := by
  intro factor factorPositive factorSmall
  let constant := 8 * (96 / Real.pi) * (2304 / (factor / 8) ^ 2)
  refine ⟨constant, by dsimp only [constant]; positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_foreign_virtual_receiver_radius amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num)
      (parameterRadius := 1) (by norm_num)]
    with frequency frequencyOne virtualGeometry geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant prepared path index time inside
    radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let selected := foreignQuadrupolePatchLabels index
  let virtualRadius := factor / 39321600 * changed.location (index.val + 1)
  let distance := factor / 1600 * changed.location (index.val + 1)
  let firstCoefficient := fun (patch : Fin 4) (power : ℕ) => first.exteriorTaylorCoefficient selected
    (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time
  let secondCoefficient := fun (patch : Fin 4) (power : ℕ) => second.exteriorTaylorCoefficient selected
    (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time
  let bound := 96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2)
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith only [inside.2, path.stopBound]⟩
  have sourceRadiusEqual (source : Fin count × Fin 4) :
      (second.patch (finProdFinEquiv source)).radius = (first.patch (finProdFinEquiv source)).radius := by
    change prepared.referenceWitness.configuration.radius (finProdFinEquiv source) = prepared.configuration.radius (finProdFinEquiv source)
    rw [prepared.referenceWitness.radiusIdentity source.1 source.2, prepared.radiusIdentity source.1 source.2]
  have sideData (patch : Fin 4) :
      (Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power‖) ∧
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power‖) ≤ bound) ∧
      (Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖secondCoefficient patch power‖) ∧
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖secondCoefficient patch power‖) ≤ bound) := by
    have actualGeometry := virtualGeometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (index, patch)
    have distancePositive : 0 < distance := actualGeometry.2.1
    have ratioVirtual : 96 * virtualRadius / distance ≤ 1 / 2 := by
      apply (div_le_iff₀ distancePositive).mpr
      dsimp only [virtualRadius, distance]
      nlinarith only [mul_pos factorPositive (changed.location_pos (index.val + 1))]
    have ratioRadius : 96 * radius / distance ≤ 1 / 2 :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left radiusSmall (by norm_num : (0 : ℝ) ≤ 96)) distancePositive.le).trans ratioVirtual
    have secondIdentity : (second.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid second.patchMotion time index patch :=
      prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
    have firstIdentity : (first.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid first.patchMotion time index patch :=
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
    have secondGaps (source : Fin count × Fin 4) (different : (index, patch) ≠ source) :
        2 * (second.patch (finProdFinEquiv source)).radius +
          (factor / 8) * changed.individualInteractionDistance (index.val + 1) (source.1.val + 1) ≤
          ‖(second.patch (finProdFinEquiv (index, patch))).center time - (second.patch (finProdFinEquiv source)).center time‖ :=
      (geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (index, patch) source different).2.1
    have firstGaps (source : Fin count × Fin 4) (different : (index, patch) ≠ source) :
        2 * (first.patch (finProdFinEquiv source)).radius +
          (factor / 8) * changed.individualInteractionDistance (index.val + 1) (source.1.val + 1) ≤
          ‖(first.patch (finProdFinEquiv (index, patch))).center time - (first.patch (finProdFinEquiv source)).center time‖ := by
      have actual := (geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (index, patch) source different).2.2.1
      change 2 * (second.patch (finProdFinEquiv source)).radius + _ ≤ _ at actual
      rw [sourceRadiusEqual source] at actual
      exact actual
    exact ⟨foreign_patch_absolute_side_at_radius first changed path.evolution inside prepared.densityIdentity
        amplitudePositive frequencyOne ratioBound alphaPositive factorPositive (index, patch) firstIdentity firstGaps
        actualGeometry.2.2.2.2.2.1 radiusNonnegative ratioRadius,
      foreign_patch_absolute_side_at_radius second changed prepared.referenceWitness.evolution referenceInside prepared.referenceWitness.densityIdentity
        amplitudePositive frequencyOne ratioBound alphaPositive factorPositive (index, patch) secondIdentity secondGaps
        actualGeometry.2.2.2.2.1 radiusNonnegative ratioRadius⟩
  have pairedData (patch : Fin 4) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power - secondCoefficient patch power‖) ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power - secondCoefficient patch power‖) ≤ 2 * bound := by
    have firstData := (sideData patch).1
    have secondData := (sideData patch).2
    have triangle (power : ℕ) : (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power - secondCoefficient patch power‖ ≤
        (96 : ℝ) ^ (power + 1) * ‖firstCoefficient patch power‖ +
          (96 : ℝ) ^ (power + 1) * ‖secondCoefficient patch power‖ := by
      exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans_eq (by ring)
    have summable := Summable.of_nonneg_of_le (fun power => mul_nonneg (by positivity) (norm_nonneg _)) triangle (firstData.1.add secondData.1)
    have comparison := summable.tsum_le_tsum triangle (firstData.1.add secondData.1)
    rw [firstData.1.tsum_add secondData.1] at comparison
    exact ⟨summable, comparison.trans (by linarith only [firstData.2, secondData.2])⟩
  refine ⟨fun patch => ⟨(sideData patch).1.1, (sideData patch).2.1, (pairedData patch).1,
    (sideData patch).1.2, (sideData patch).2.2, (pairedData patch).2⟩, ?_⟩
  have finite := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => (pairedData patch).2)
  apply finite.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [bound, constant]
  ring

end EulerNonuniqueness.Paper
