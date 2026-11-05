import EulerNonuniqueness.Section6.MovingQuadrupoleRelativeSeries

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem incoming_series_normalization
    {gap receiverScale sourceScale length centered moment translation raw observer constant : ℝ}
    (gapPositive : 0 < gap) (sourcePositive : 0 < sourceScale)
    (gapOne : gap ≤ 1) (sourceOne : sourceScale ≤ 1) (gapReceiver : gap ≤ receiverScale)
    (sourceGap : sourceScale ≤ 3 * gap) (lengthGap : length ≤ gap)
    (centeredNonnegative : 0 ≤ centered)
    (momentNonnegative : 0 ≤ moment) (translationNonnegative : 0 ≤ translation)
    (rawNonnegative : 0 ≤ raw) (observerNonnegative : 0 ≤ observer) (constantNonnegative : 0 ≤ constant) :
    96 * (266240 * (gap / sourceScale) * moment + 3145728 * centered +
      262144 * (observer + sourceScale * translation) +
      1207959552 * ((observer + sourceScale * translation) / gap)) +
      8 * (1024 * 96 * 8 ^ 5 * ((observer + sourceScale * translation + 4 * length * centered) / gap) +
        9216 * constant * 96 * 8 ^ 4 * raw) ≤
      1000000000000000 * (constant + 1) *
        ((1 + receiverScale / sourceScale) * (centered + moment + translation + raw) + observer / gap) := by
  let state := centered + moment + translation + raw
  let bound := (1 + receiverScale / sourceScale) * state + observer / gap
  have stateNonnegative : 0 ≤ state := by dsimp only [state]; positivity
  have receiverNonnegative : 0 ≤ receiverScale := gapPositive.le.trans gapReceiver
  have weighted : state ≤ (1 + receiverScale / sourceScale) * state :=
    le_mul_of_one_le_left stateNonnegative (by linarith only [div_nonneg receiverNonnegative sourcePositive.le])
  have stateBound : state ≤ bound := weighted.trans (le_add_of_nonneg_right (by positivity))
  have observerBound : observer / gap ≤ bound := le_add_of_nonneg_left (by positivity)
  have boundNonnegative : 0 ≤ bound := stateNonnegative.trans stateBound
  have centeredState : centered ≤ state := by dsimp only [state]; linarith only [momentNonnegative, translationNonnegative, rawNonnegative]
  have rawState : raw ≤ state := by dsimp only [state]; linarith only [centeredNonnegative, momentNonnegative, translationNonnegative]
  have centeredBound : centered ≤ bound := centeredState.trans stateBound
  have rawBound : raw ≤ bound := rawState.trans stateBound
  have translationState : translation ≤ state := by dsimp only [state]; linarith only [centeredNonnegative, momentNonnegative, rawNonnegative]
  have momentState : moment ≤ state := by dsimp only [state]; linarith only [centeredNonnegative, translationNonnegative, rawNonnegative]
  have momentBound : gap / sourceScale * moment ≤ bound := by
    have first := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right gapReceiver sourcePositive.le) momentNonnegative
    have second := mul_le_mul_of_nonneg_left momentState (div_nonneg receiverNonnegative sourcePositive.le)
    have third : receiverScale / sourceScale * state ≤ (1 + receiverScale / sourceScale) * state := by
      rw [add_mul, one_mul]
      exact le_add_of_nonneg_left stateNonnegative
    exact (first.trans (second.trans third)).trans (le_add_of_nonneg_right (by positivity))
  have observerBelow : observer ≤ observer / gap := (le_div_iff₀ gapPositive).mpr
    (mul_le_of_le_one_right observerNonnegative gapOne)
  have centerBound : observer + sourceScale * translation ≤ 2 * bound := by
    have translated := (mul_le_of_le_one_left translationNonnegative sourceOne).trans (translationState.trans stateBound)
    linarith only [observerBelow.trans observerBound, translated]
  have sourceRatio : sourceScale / gap ≤ 3 := (div_le_iff₀ gapPositive).mpr sourceGap
  have lengthRatio : length / gap ≤ 1 := (div_le_one gapPositive).mpr lengthGap
  have centerRatioBound : (observer + sourceScale * translation) / gap ≤ 4 * bound := by
    have translated := mul_le_mul sourceRatio (translationState.trans stateBound) translationNonnegative (by norm_num : (0 : ℝ) ≤ 3)
    have identity : (observer + sourceScale * translation) / gap = observer / gap + (sourceScale / gap) * translation := by ring
    rw [identity]
    linarith only [translated, observerBound]
  have completeRatioBound : (observer + sourceScale * translation + 4 * length * centered) / gap ≤ 8 * bound := by
    have offset := mul_le_mul lengthRatio centeredBound centeredNonnegative (by norm_num : (0 : ℝ) ≤ 1)
    have identity : (observer + sourceScale * translation + 4 * length * centered) / gap =
        (observer + sourceScale * translation) / gap + 4 * ((length / gap) * centered) := by ring
    rw [identity]
    linarith only [centerRatioBound, offset]
  have first := mul_le_mul_of_nonneg_left momentBound (by norm_num : (0 : ℝ) ≤ 266240)
  have second := mul_le_mul_of_nonneg_left centeredBound (by norm_num : (0 : ℝ) ≤ 3145728)
  have third := mul_le_mul_of_nonneg_left centerBound (by norm_num : (0 : ℝ) ≤ 262144)
  have fourth := mul_le_mul_of_nonneg_left centerRatioBound (by norm_num : (0 : ℝ) ≤ 1207959552)
  have fifth := mul_le_mul_of_nonneg_left completeRatioBound (by norm_num : (0 : ℝ) ≤ 1024 * 96 * 8 ^ 5)
  have sixth := mul_le_mul_of_nonneg_left rawBound (show 0 ≤ 9216 * constant * 96 * 8 ^ 4 by positivity)
  change _ ≤ 1000000000000000 * (constant + 1) * bound
  have estimate : 96 * (266240 * (gap / sourceScale) * moment + 3145728 * centered +
      262144 * (observer + sourceScale * translation) + 1207959552 * ((observer + sourceScale * translation) / gap)) +
      8 * (1024 * 96 * 8 ^ 5 * ((observer + sourceScale * translation + 4 * length * centered) / gap) +
        9216 * constant * 96 * 8 ^ 4 * raw) ≤
      96 * (266240 * bound + 3145728 * bound + 262144 * (2 * bound) + 1207959552 * (4 * bound)) +
      8 * (1024 * 96 * 8 ^ 5 * (8 * bound) + 9216 * constant * 96 * 8 ^ 4 * bound) := by
    linear_combination 96 * first + 96 * second + 96 * third + 96 * fourth + 8 * fifth + 8 * sixth
  have polynomial (value coefficient : ℝ) (valueNonnegative : 0 ≤ value) (coefficientNonnegative : 0 ≤ coefficient) :
      96 * (266240 * value + 3145728 * value + 262144 * (2 * value) + 1207959552 * (4 * value)) +
        8 * (1024 * 96 * 8 ^ 5 * (8 * value) + 9216 * coefficient * 96 * 8 ^ 4 * value) ≤
      1000000000000000 * (coefficient + 1) * value := by
    nlinarith only [valueNonnegative, mul_nonneg coefficientNonnegative valueNonnegative]
  exact estimate.trans (polynomial bound constant boundNonnegative constantNonnegative)

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem incoming_quadrupole_series_envelope_le
    (comparison : MovingPatchFamilySourceComparison 4) (firstCenter secondCenter : ℂ)
    {circulation constant gap receiverScale sourceScale length centered moment translation raw observer : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (constantNonnegative : 0 ≤ constant)
    (gapPositive : 0 < gap) (sourcePositive : 0 < sourceScale) (lengthPositive : 0 < length)
    (gapOne : gap ≤ 1) (sourceOne : sourceScale ≤ 1) (gapReceiver : gap ≤ receiverScale)
    (sourceGap : sourceScale ≤ 3 * gap) (lengthGap : length ≤ gap)
    (centeredNonnegative : 0 ≤ centered) (momentNonnegative : 0 ≤ moment)
    (translationNonnegative : 0 ≤ translation) (rawNonnegative : 0 ≤ raw) (observerNonnegative : 0 ≤ observer)
    (ratioSmall : 8 * 96 * comparison.receiverRadius / (gap / 8) ≤ 1 / 2)
    (momentDifference : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
      fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ ≤ length ^ 2 / sourceScale * moment)
    (referenceMoment : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)‖ ≤ length ^ 2)
    (positionDifference : (∑ patch : Fin 4, ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
      ((comparison.second.patch patch).center comparison.time - secondCenter)‖) ≤ 4 * length * centered)
    (positions : (∑ patch : Fin 4, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) ≤ 12 * length)
    (combined : ‖(comparison.firstReceiver comparison.time - firstCenter) -
      (comparison.secondReceiver comparison.time - secondCenter)‖ ≤ gap)
    (combinedSplit : ‖(comparison.firstReceiver comparison.time - firstCenter) -
      (comparison.secondReceiver comparison.time - secondCenter)‖ ≤ observer + sourceScale * translation)
    (mass : ∀ patch, |(comparison.source patch).density| * (comparison.source patch).first.radius ^ 2 ≤ circulation)
    (radii : ∀ patch, (comparison.source patch).first.radius ≤ length)
    (separated : ∀ patch, gap / 8 ≤ ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center comparison.time‖)
    (displacements : ∀ patch, ‖(comparison.source patch).displacementDifference‖ ≤ observer + sourceScale * translation + 4 * length * centered)
    (spectral : ∀ patch, (comparison.source patch).spectralDifferenceBudget ≤ raw) :
    comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter (3 * length) (gap / 8) 96 +
      2 * ∑ patch : Fin 4, ((comparison.source patch).centroidCorrectionCenterEnvelope (gap / 8) 96 +
        (comparison.source patch).centeredShapeDifferenceEnvelope constant 96) ≤
      1000000000000000 * (constant + 1) * (circulation * length ^ 2 / gap ^ 4 *
        (1 + receiverScale / sourceScale) * (centered + moment + translation + raw) +
          circulation * length ^ 2 / gap ^ 5 * observer) := by
  let firstMoment := fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)
  let secondMoment := fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)
  let displacement := ‖(comparison.firstReceiver comparison.time - firstCenter) - (comparison.secondReceiver comparison.time - secondCenter)‖
  have distancePositive : 0 < gap / 8 := by positivity
  have coefficientBound : |circulation| / (2 * Real.pi) ≤ circulation := by
    rw [abs_of_nonneg circulationNonnegative]
    exact div_le_self circulationNonnegative (by linarith [Real.pi_gt_three])
  have receiverRadiusNonnegative := comparison.receiverRadius_nonnegative
  have ratioNonnegative : 0 ≤ 96 * comparison.receiverRadius / (gap / 8) := by positivity
  have firstDenominator : (1 / 2 : ℝ) ≤ 1 - 4 * 96 * comparison.receiverRadius / (gap / 8) := by
    have identity : 4 * 96 * comparison.receiverRadius / (gap / 8) = (8 * 96 * comparison.receiverRadius / (gap / 8)) / 2 := by ring
    rw [identity]
    linarith only [ratioSmall]
  have secondDenominator : (1 / 2 : ℝ) ≤ 1 - 8 * 96 * comparison.receiverRadius / (gap / 8) := by linarith only [ratioSmall]
  have firstInverse : (1 - 4 * 96 * comparison.receiverRadius / (gap / 8))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) firstDenominator
  have secondInverse : (1 - 8 * 96 * comparison.receiverRadius / (gap / 8))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) secondDenominator
  have momentBound : ‖secondMoment‖ ≤ length ^ 2 + length ^ 2 / sourceScale * moment := by
    have triangle := norm_add_le firstMoment (secondMoment - firstMoment)
    have identity : firstMoment + (secondMoment - firstMoment) = secondMoment := by abel
    rw [identity, norm_sub_rev] at triangle
    exact triangle.trans (add_le_add referenceMoment momentDifference)
  have momentProduct : ‖secondMoment‖ * displacement ≤ length ^ 2 * (observer + sourceScale * translation) +
      (length ^ 2 / sourceScale * moment) * gap := by
    have initial := mul_le_mul_of_nonneg_right momentBound (show 0 ≤ displacement from norm_nonneg _)
    have first := mul_le_mul_of_nonneg_left combinedSplit (sq_nonneg length)
    have second := mul_le_mul_of_nonneg_left combined (show 0 ≤ length ^ 2 / sourceScale * moment by positivity)
    exact initial.trans (by nlinarith only [first, second])
  have pointCoarse : comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter (3 * length) (gap / 8) 96 ≤
      circulation * 96 * (8 * (gap / 8)⁻¹ ^ 3 * (length ^ 2 / sourceScale * moment) +
        64 * (gap / 8)⁻¹ ^ 4 * (3 * length) * (4 * length * centered) +
        64 * (gap / 8)⁻¹ ^ 4 * (length ^ 2 * (observer + sourceScale * translation) +
          (length ^ 2 / sourceScale * moment) * gap) +
        1024 * (gap / 8)⁻¹ ^ 5 * (3 * length) * (12 * length) * (observer + sourceScale * translation)) := by
    have initial : comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter (3 * length) (gap / 8) 96 ≤
        (96 * circulation * (4 * (gap / 8)⁻¹ ^ 3 * ‖firstMoment - secondMoment‖ +
          32 * (gap / 8)⁻¹ ^ 4 * (3 * length) * ∑ patch : Fin 4,
            ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
              ((comparison.second.patch patch).center comparison.time - secondCenter)‖)) * 2 +
        (96 * circulation * (32 * (gap / 8)⁻¹ ^ 4 * ‖secondMoment‖ +
          512 * (gap / 8)⁻¹ ^ 5 * (3 * length) * ∑ patch : Fin 4,
            ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) * displacement) * 2 := by
      unfold MovingPatchFamilySourceComparison.quadrupolePointDifferenceEnvelope
      gcongr
    apply initial.trans
    have identity : (96 * circulation * (4 * (gap / 8)⁻¹ ^ 3 * ‖firstMoment - secondMoment‖ +
        32 * (gap / 8)⁻¹ ^ 4 * (3 * length) * ∑ patch : Fin 4,
          ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
            ((comparison.second.patch patch).center comparison.time - secondCenter)‖)) * 2 +
      (96 * circulation * (32 * (gap / 8)⁻¹ ^ 4 * ‖secondMoment‖ +
        512 * (gap / 8)⁻¹ ^ 5 * (3 * length) * ∑ patch : Fin 4,
          ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) * displacement) * 2 =
      circulation * 96 * (8 * (gap / 8)⁻¹ ^ 3 * ‖firstMoment - secondMoment‖ +
        64 * (gap / 8)⁻¹ ^ 4 * (3 * length) * (∑ patch : Fin 4,
          ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
            ((comparison.second.patch patch).center comparison.time - secondCenter)‖) +
        64 * (gap / 8)⁻¹ ^ 4 * (‖secondMoment‖ * displacement) +
        1024 * (gap / 8)⁻¹ ^ 5 * (3 * length) * (∑ patch : Fin 4,
          ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) * displacement) := by ring
    rw [identity]
    gcongr
  have patchBound (patch : Fin 4) :
      (comparison.source patch).centroidCorrectionCenterEnvelope (gap / 8) 96 +
        (comparison.source patch).centeredShapeDifferenceEnvelope constant 96 ≤
      circulation * length ^ 2 / gap ^ 4 * (1024 * 96 * 8 ^ 5 *
        ((observer + sourceScale * translation + 4 * length * centered) / gap) +
          9216 * constant * 96 * 8 ^ 4 * raw) := by
    let source := comparison.source patch
    let distance := ‖source.secondReceiver - source.second.center comparison.time‖
    have actualPositive : 0 < distance := distancePositive.trans_le (separated patch)
    have fourthMoment : |source.density| * source.first.radius ^ 4 ≤ circulation * length ^ 2 := by
      calc
        _ = (|source.density| * source.first.radius ^ 2) * source.first.radius ^ 2 := by ring
        _ ≤ circulation * source.first.radius ^ 2 := mul_le_mul_of_nonneg_right (mass patch) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ source.first.radius_positive.le (radii patch) 2) circulationNonnegative
    have centerBound : source.centroidCorrectionCenterEnvelope (gap / 8) 96 ≤
        1024 * 96 * circulation * length ^ 2 * (gap / 8)⁻¹ ^ 5 *
          (observer + sourceScale * translation + 4 * length * centered) := by
      unfold MovingPatchSourceComparison.centroidCorrectionCenterEnvelope
      have scaled := mul_le_mul_of_nonneg_left fourthMoment (show 0 ≤ 1024 * 96 * (gap / 8)⁻¹ ^ 5 by positivity)
      have actual := mul_le_mul scaled (displacements patch) (norm_nonneg _) (by positivity)
      convert actual using 1 <;> ring
    have inverseFourth : distance⁻¹ ^ 4 ≤ (gap / 8)⁻¹ ^ 4 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ distancePositive (separated patch)) 4
    have shapeIdentity : source.centeredShapeDifferenceEnvelope constant 96 =
        (9216 * constant * 96 / (2 * Real.pi)) * (|source.density| * source.first.radius ^ 2) *
          source.first.radius ^ 2 * distance⁻¹ ^ 4 * source.spectralDifferenceBudget := by
      unfold MovingPatchSourceComparison.centeredShapeDifferenceEnvelope
      have timeIdentity : source.time = comparison.time := rfl
      rw [timeIdentity]
      dsimp only [distance]
      ring
    have shapeBound : source.centeredShapeDifferenceEnvelope constant 96 ≤
        9216 * constant * 96 * circulation * length ^ 2 * (gap / 8)⁻¹ ^ 4 * raw := by
      rw [shapeIdentity]
      have scalarBound : 9216 * constant * 96 / (2 * Real.pi) ≤ 9216 * constant * 96 :=
        div_le_self (by positivity) (by linarith [Real.pi_gt_three])
      have radiusSquared := pow_le_pow_left₀ source.first.radius_positive.le (radii patch) 2
      have budgetNonnegative := source.spectralDifferenceBudget_nonnegative
      have massBound : |source.density| * source.first.radius ^ 2 ≤ circulation := mass patch
      have spectralBound : source.spectralDifferenceBudget ≤ raw := spectral patch
      gcongr
    apply (add_le_add centerBound shapeBound).trans_eq
    field_simp [gapPositive.ne']; ring
  have patches := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => patchBound patch)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at patches
  have combinedBound := add_le_add pointCoarse (mul_le_mul_of_nonneg_left patches (by norm_num : (0 : ℝ) ≤ 2))
  norm_num only [Nat.cast_ofNat] at combinedBound
  have identity : circulation * 96 * (8 * (gap / 8)⁻¹ ^ 3 * (length ^ 2 / sourceScale * moment) +
      64 * (gap / 8)⁻¹ ^ 4 * (3 * length) * (4 * length * centered) +
      64 * (gap / 8)⁻¹ ^ 4 * (length ^ 2 * (observer + sourceScale * translation) +
        (length ^ 2 / sourceScale * moment) * gap) +
      1024 * (gap / 8)⁻¹ ^ 5 * (3 * length) * (12 * length) * (observer + sourceScale * translation)) +
      2 * (4 * (circulation * length ^ 2 / gap ^ 4 * (1024 * 96 * 8 ^ 5 *
        ((observer + sourceScale * translation + 4 * length * centered) / gap) +
          9216 * constant * 96 * 8 ^ 4 * raw))) =
      circulation * length ^ 2 / gap ^ 4 * (96 * (266240 * (gap / sourceScale) * moment +
        3145728 * centered + 262144 * (observer + sourceScale * translation) +
        1207959552 * ((observer + sourceScale * translation) / gap)) +
        8 * (1024 * 96 * 8 ^ 5 * ((observer + sourceScale * translation + 4 * length * centered) / gap) +
          9216 * constant * 96 * 8 ^ 4 * raw)) := by
    field_simp [gapPositive.ne', sourcePositive.ne']; ring
  norm_num only [Nat.cast_ofNat] at identity
  rw [identity] at combinedBound
  have normalized := incoming_series_normalization gapPositive sourcePositive gapOne sourceOne gapReceiver sourceGap lengthGap
    centeredNonnegative momentNonnegative translationNonnegative rawNonnegative observerNonnegative constantNonnegative
  norm_num only [Nat.cast_ofNat] at normalized
  have scaled := mul_le_mul_of_nonneg_left normalized (show 0 ≤ circulation * length ^ 2 / gap ^ 4 by positivity)
  exact combinedBound.trans (scaled.trans_eq (by field_simp [gapPositive.ne']; ring))

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

