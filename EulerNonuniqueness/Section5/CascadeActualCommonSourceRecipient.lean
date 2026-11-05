import EulerNonuniqueness.Section5.CascadeActualCenteredSourceSeries
import EulerNonuniqueness.Section3.CanonicalExteriorCommonSourceRecipient

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_cascade_common_source_recipient :
    ∃ sourceRadius > (0 : ℝ), ∃ fieldRadius > (0 : ℝ),
      ∃ shapeConstant ≥ (0 : ℝ), ∃ fieldConstant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {rawCap scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop),
      ∀ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      ∀ receiver : Fin count × Fin 4,
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let selected := Finset.univ.erase (finProdFinEquiv receiver)
      let firstDistance := 192 * (comparison.first.patch (finProdFinEquiv receiver)).radius
      let finalDistance := 192 * (comparison.second.patch (finProdFinEquiv receiver)).radius
      let distance := fun source : Fin (count * 4) => (factor / 8) *
        ({scales with frequency := frequency} : Scales).individualInteractionDistance
          (receiver.1.val + 1) ((finProdFinEquiv.symm source).1.val + 1)
      (∀ source ∈ selected, ∀ position ∈ (comparison.first.patch source).domain time,
        firstDistance ≤ ‖(comparison.first.patch (finProdFinEquiv receiver)).center time - position‖) ∧
      (∀ source ∈ selected, ∀ position ∈ (comparison.second.patch source).domain time,
        finalDistance ≤ ‖(comparison.second.patch (finProdFinEquiv receiver)).center time - position‖) ∧
      ∀ (firstSeparated : ∀ source ∈ selected, ∀ position ∈ (comparison.first.patch source).domain time,
          firstDistance ≤ ‖(comparison.first.patch (finProdFinEquiv receiver)).center time - position‖)
        (finalSeparated : ∀ source ∈ selected, ∀ position ∈ (comparison.second.patch source).domain time,
          finalDistance ≤ ‖(comparison.second.patch (finProdFinEquiv receiver)).center time - position‖)
        (commonPhase : Circle) (data : PeriodicC1HolderHalf), ‖data - standardCircleBanach‖ ≤ fieldRadius →
      ∀ operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf,
      ‖operator
        (comparison.first.canonicalProjectedExteriorContourField (finProdFinEquiv receiver) time firstDistance
            (by exact mul_pos (by norm_num) (comparison.first.patch _).radius_positive)
            (by dsimp only [firstDistance]; linarith [(comparison.first.patch (finProdFinEquiv receiver)).radius_positive])
            firstSeparated commonPhase data -
          comparison.second.canonicalProjectedExteriorContourField (finProdFinEquiv receiver) time finalDistance
            (by exact mul_pos (by norm_num) (comparison.second.patch _).radius_positive)
            (by dsimp only [finalDistance]; linarith [(comparison.second.patch (finProdFinEquiv receiver)).radius_positive])
            finalSeparated commonPhase data)‖ ≤
      2 * fieldConstant * ‖operator‖ * ∑ source ∈ selected,
        ((comparison.source source).centerDifferenceEnvelope (distance source) 96 +
          (comparison.source source).centeredShapeDifferenceEnvelope shapeConstant 96) := by
  obtain ⟨sourceRadius, sourcePositive, shapeConstant, shapeNonnegative, sourceSeries⟩ :=
    exists_uniform_actual_cascade_centered_source_series
  obtain ⟨fieldRadius, fieldPositive, fieldConstant, fieldNonnegative, recipient⟩ :=
    FiniteMovingPatchFamily.canonicalProjectedExteriorContourField_exists_common_source_recipient_ball
  refine ⟨sourceRadius, sourcePositive, fieldRadius, fieldPositive, shapeConstant, shapeNonnegative,
    fieldConstant, fieldNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [sourceSeries scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative
      factorPositive factorSmall (by norm_num : (0 : ℝ) < 96),
    scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall (by norm_num : (0 : ℝ) < 96)
      (by norm_num : (0 : ℝ) < 1)] with frequency series geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant prepared path time inside shapes receiver
  dsimp only
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let selected : Finset (Fin (count * 4)) := Finset.univ.erase (finProdFinEquiv receiver)
  let firstDistance := 192 * (comparison.first.patch (finProdFinEquiv receiver)).radius
  let finalDistance := 192 * (comparison.second.patch (finProdFinEquiv receiver)).radius
  let distance := fun source : Fin (count * 4) => (factor / 8) *
    ({scales with frequency := frequency} : Scales).individualInteractionDistance
      (receiver.1.val + 1) ((finProdFinEquiv.symm source).1.val + 1)
  have actualGeometry (source : Fin (count * 4)) (member : source ∈ selected) :=
    geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside
      receiver (finProdFinEquiv.symm source) (by
        intro equality
        have equalLabels := congrArg finProdFinEquiv equality
        rw [Equiv.apply_symm_apply] at equalLabels
        exact (Finset.mem_erase.mp member).1 equalLabels.symm)
  have radiusScale (source : Fin (count * 4)) (member : source ∈ selected) : firstDistance ≤ distance source := by
    have actual := actualGeometry source member
    have multiplied := (div_le_iff₀ actual.1).mp actual.2.2.2.1
    change 2 * 96 * (comparison.first.patch (finProdFinEquiv receiver)).radius ≤
      1 / 2 * distance source at multiplied
    dsimp only [firstDistance]
    linarith [(comparison.first.patch (finProdFinEquiv receiver)).radius_positive]
  have firstSeparated : ∀ source ∈ selected, ∀ position ∈ (comparison.first.patch source).domain time,
      firstDistance ≤ ‖(comparison.first.patch (finProdFinEquiv receiver)).center time - position‖ := by
    intro source member position positionInside
    have actual := actualGeometry source member
    have gap := actual.2.1
    have sourceBound := (comparison.first.patch source).domain_subset_ball_two_radius time positionInside
    have sourceNorm : ‖position - (comparison.first.patch source).center time‖ <
        2 * (comparison.first.patch source).radius := by simpa only [mem_ball, dist_eq_norm] using sourceBound
    have triangle : ‖(comparison.first.patch (finProdFinEquiv receiver)).center time -
        (comparison.first.patch source).center time‖ ≤
        ‖(comparison.first.patch (finProdFinEquiv receiver)).center time - position‖ +
          ‖position - (comparison.first.patch source).center time‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        ((comparison.first.patch (finProdFinEquiv receiver)).center time - position)
        (position - (comparison.first.patch source).center time)
    simp only [Equiv.apply_symm_apply] at gap
    change 2 * (comparison.first.patch source).radius + distance source ≤
      ‖(comparison.first.patch (finProdFinEquiv receiver)).center time - (comparison.first.patch source).center time‖ at gap
    exact (radiusScale source member).trans (by linarith)
  have finalSeparated : ∀ source ∈ selected, ∀ position ∈ (comparison.second.patch source).domain time,
      finalDistance ≤ ‖(comparison.second.patch (finProdFinEquiv receiver)).center time - position‖ := by
    intro source member position positionInside
    have actual := actualGeometry source member
    have gap := actual.2.2.1
    have sourceBound := (comparison.second.patch source).domain_subset_ball_two_radius time positionInside
    have sourceNorm : ‖position - (comparison.second.patch source).center time‖ <
        2 * (comparison.second.patch source).radius := by simpa only [mem_ball, dist_eq_norm] using sourceBound
    have triangle : ‖(comparison.second.patch (finProdFinEquiv receiver)).center time -
        (comparison.second.patch source).center time‖ ≤
        ‖(comparison.second.patch (finProdFinEquiv receiver)).center time - position‖ +
          ‖position - (comparison.second.patch source).center time‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        ((comparison.second.patch (finProdFinEquiv receiver)).center time - position)
        (position - (comparison.second.patch source).center time)
    rw [← comparison.radiusEqual source] at sourceNorm
    simp only [Equiv.apply_symm_apply] at gap
    change 2 * (comparison.first.patch source).radius + distance source ≤
      ‖(comparison.second.patch (finProdFinEquiv receiver)).center time - (comparison.second.patch source).center time‖ at gap
    have radiusIdentity : finalDistance = firstDistance := by
      dsimp only [firstDistance, finalDistance]
      rw [comparison.radiusEqual]
    rw [radiusIdentity]
    exact (radiusScale source member).trans (by linarith)
  refine ⟨firstSeparated, finalSeparated, ?_⟩
  intro firstGap finalGap commonPhase data dataInside operator
  have actualSeries := series count orbit sectionTime phase dipoleAngle prepared path inside shapes receiver
  have bound := recipient comparison.first comparison.second (finProdFinEquiv receiver) (finProdFinEquiv receiver)
    time firstDistance finalDistance
    (mul_pos (by norm_num) (comparison.first.patch _).radius_positive)
    (mul_pos (by norm_num) (comparison.second.patch _).radius_positive)
    (le_refl _) (le_refl _) firstGap finalGap commonPhase data dataInside operator
  have coefficientIdentity (degree : ℕ) : comparison.second.canonicalExteriorStaticCoefficient
      (finProdFinEquiv receiver) time degree =
      comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (degree + 1) time := by
    dsimp only [FiniteMovingPatchFamily.canonicalExteriorStaticCoefficient]
    rw [← comparison.radiusEqual (finProdFinEquiv receiver)]
    rfl
  simp_rw [coefficientIdentity] at bound
  have scalar := mul_le_mul_of_nonneg_left actualSeries.2 (mul_nonneg fieldNonnegative (norm_nonneg operator))
  exact bound.trans (scalar.trans_eq (by ring))

end EulerNonuniqueness.Paper
