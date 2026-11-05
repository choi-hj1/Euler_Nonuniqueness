import EulerNonuniqueness.Section5.CascadeActualQuadrupoleFixedMacroSeries
import EulerNonuniqueness.Section5.CascadeActualStrongFirstMoment
import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem incoming_normalization
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

private theorem incoming_comparison_bound
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
  have normalized := incoming_normalization gapPositive sourcePositive gapOne sourceOne gapReceiver sourceGap lengthGap
    centeredNonnegative momentNonnegative translationNonnegative rawNonnegative observerNonnegative constantNonnegative
  norm_num only [Nat.cast_ofNat] at normalized
  have scaled := mul_le_mul_of_nonneg_left normalized (show 0 ≤ circulation * length ^ 2 / gap ^ 4 by positivity)
  exact combinedBound.trans (scaled.trans_eq (by field_simp [gapPositive.ne']; ring))

theorem exists_uniform_actual_incoming_source_block_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 8 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val < source.val → source.val + 1 < count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time source| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish, ∀ radius : ℝ, 0 ≤ radius →
    radius ≤ scales.location (receiver.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily
    let reference := prepared.referenceWitness.trajectory.movingFamily
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let state := prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed alternative.patchMotion prepared.reference source time‖ +
      ‖quadrupoleCenter alternative.patchMotion time source - quadrupoleCenter reference.patchMotion time source‖ /
        changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let term := fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter alternative.patchMotion current receiver) radius (power + 1) time -
        (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter reference.patchMotion current receiver) radius (power + 1) time‖
    Summable term ∧ (∑' power : ℕ, term power) ≤
      constant * (changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
        (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state +
          changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
            ‖quadrupoleCenter alternative.patchMotion time receiver - quadrupoleCenter reference.patchMotion time receiver‖) := by
  obtain ⟨sourceRadius, sourcePositive, baseConstant, baseNonnegative, factory⟩ :=
    exists_uniform_actual_foreign_quadrupole_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨rawCap, rawPositive, 1000000000000000 * (baseConstant + 1), by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have referenceDecay : Tendsto (fun frequency : ℝ => 4 * referenceConstant *
      ({scales with frequency := frequency} : Scales).hessian *
      Real.exp (referenceConstant * ({scales with frequency := frequency} : Scales).strain)) atTop (𝓝 0) := by
    have exponentialDecay : Tendsto (fun frequency : ℝ =>
        Real.exp (referenceConstant * ({scales with frequency := frequency} : Scales).strain)) atTop
        (𝓝 (Real.exp (referenceConstant * 0))) :=
      Real.continuous_exp.continuousAt.tendsto.comp
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul referenceConstant)
    simpa using ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (4 * referenceConstant)).mul exponentialDecay
  filter_upwards [factory 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) thresholdSmall referenceNonnegative,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 300),
    referenceDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency estimates extents alignment radii lengths referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered nonterminal finish finishNonnegative finishBound
    radialSmall time inside radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let firstCenter := quadrupoleCenter first time source
  let secondCenter := quadrupoleCenter second time source
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let length := changed.length (source.val + 1)
  let shapes := actualShapes prepared path time ⟨inside.1, inside.2.trans finishBound⟩
  let original := (prepared.sourceComparison path ⟨inside.1, inside.2.trans finishBound⟩ (finProdFinEquiv (receiver, 0)) shapes).quadrupole source
  let comparison : MovingPatchFamilySourceComparison 4 :=
    {original with
      firstReceiver := fun current => quadrupoleCenter first current receiver
      secondReceiver := fun current => quadrupoleCenter second current receiver
      receiverRadius := radius
      receiverRadius_nonnegative := radiusNonnegative}
  let centered := prepared.rawSourceCenteredState time source
  let moment := ‖relativeNormalizedFirstMoment changed second prepared.reference source time‖
  let translation := ‖firstCenter - secondCenter‖ / changed.location (source.val + 1)
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let observer := ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [fullInside.2, path.stopBound]⟩
  have different : receiver ≠ source := fun same => by simp only [same, lt_self_iff_false] at ordered
  have differentIndices : receiver.val + 1 ≠ source.val + 1 := fun same => different (Fin.ext (Nat.add_right_cancel same))
  have gapPositive : 0 < gap := changed.location_distance_pos differentIndices
  have sourcePositive := changed.location_pos (source.val + 1)
  have receiverPositive := changed.location_pos (receiver.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have sourceBelow := changed.location_antitone (show receiver.val + 1 ≤ source.val + 1 by omega)
  have gapIdentity : gap = changed.location (receiver.val + 1) - changed.location (source.val + 1) := abs_of_nonneg (sub_nonneg.mpr sourceBelow)
  have gapReceiver : gap ≤ changed.location (receiver.val + 1) := by rw [gapIdentity]; linarith only [sourcePositive]
  have gapOne : gap ≤ 1 := gapReceiver.trans (changed.location_le_one _)
  have locations := changed.location_sum_le_three_distance differentIndices
  have sourceGap : changed.location (source.val + 1) ≤ 3 * gap := by linarith only [locations, receiverPositive]
  have receiverGap : changed.location (receiver.val + 1) ≤ 3 * gap := by linarith only [locations, sourcePositive]
  have lengthSmall : length ≤ changed.location (source.val + 1) / 300 := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (source.val + 1)).le
  have sourceRadiusSmall : 3 * length ≤ scales.location (source.val + 1) / 100 := by
    change 3 * length ≤ changed.location (source.val + 1) / 100
    linarith only [lengthSmall]
  have lengthGap : length ≤ gap := by linarith only [lengthSmall, sourceGap, gapPositive]
  have physicalSmall : changed.radius (source.val + 1) ≤ length := by simpa only [one_mul] using (radii (source.val + 1)).le
  have extent := extents prepared.toCascadeMaterialPreparedPair path factorSmall source nonterminal finish finishNonnegative
    finishBound radialSmall time inside
  have firstCenters (patch : Fin 4) : (comparison.first.patch patch).center time = patchCentroid first time source patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have secondCenters (patch : Fin 4) : (comparison.second.patch patch).center time = patchCentroid second time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have sourcePositions (patch : Fin 4) :
      ‖(comparison.first.patch patch).center time - firstCenter‖ ≤ 3 * length ∧
      ‖(comparison.second.patch patch).center time - secondCenter‖ ≤ 3 * length := by
    rw [firstCenters, secondCenters]
    exact ⟨(extent patch).2, (extent patch).1⟩
  have seriesActual := estimates count phase dipoleAngle prepared path fullInside shapes receiver source different
    (3 * length) (by positivity) sourceRadiusSmall (fun patch => (extent patch).2) (fun patch => (extent patch).1)
    radius radiusNonnegative (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using radiusSmall)
  have positions : (∑ patch : Fin 4, ‖(comparison.second.patch patch).center time - secondCenter‖) ≤ 12 * length := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => (sourcePositions patch).2)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
    convert summed using 1; ring
  have positionDifference : (∑ patch : Fin 4, ‖((comparison.first.patch patch).center time - firstCenter) -
      ((comparison.second.patch patch).center time - secondCenter)‖) ≤ 4 * length * centered := by
    have actual := prepared.sourceComparison_quadrupole_centered_difference_sum_le path fullInside
      (finProdFinEquiv (receiver, 0)) shapes source
    apply actual.trans_eq
    dsimp only [centered, CascadeSourcePreparedPair.rawSourceCenteredState, length]
    field_simp [(changed.length_pos _).ne']; ring
  have momentDifference : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter) -
      fourPointSignedMoment (fun patch => (comparison.second.patch patch).center time - secondCenter)‖ =
      length ^ 2 / changed.location (source.val + 1) * moment :=
    prepared.sourceComparison_quadrupole_signed_moment_difference_norm path fullInside (finProdFinEquiv (receiver, 0)) shapes source firstCenter secondCenter
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have referenceMoment : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter)‖ ≤ length ^ 2 := by
    have signed := prepared.sourceComparison_quadrupole_first_signed_moment path fullInside (finProdFinEquiv (receiver, 0)) shapes source firstCenter
    change fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter) =
      4 * centroidAsymmetry first time source at signed
    rw [signed, norm_mul]
    norm_num only [Complex.norm_ofNat]
    have coarse := (prepared.referenceWitness.coarse.2.1 time
      (show time ∈ Icc (0 : ℝ) 2 from ⟨inside.1, fullInside.2.trans (path.stopBound.trans (by norm_num))⟩) source).2.2.2.2.1
    have timeOne : time ≤ 1 := fullInside.2.trans path.stopBound
    have exponential : Real.exp (referenceConstant * changed.strain * time) ≤ Real.exp (referenceConstant * changed.strain) :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_right (mul_nonneg referenceNonnegative strainNonnegative) timeOne)
    have timeExponential := mul_le_mul timeOne exponential (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
    have scaled := mul_le_mul_of_nonneg_left timeExponential (show 0 ≤ 4 * referenceConstant * changed.hessian by positivity)
    have normalized : 4 * ‖centroidAsymmetry first time source‖ ≤
        (4 * referenceConstant * changed.hessian * Real.exp (referenceConstant * changed.strain)) * length ^ 2 := by
      have firstBound := mul_le_mul_of_nonneg_left coarse (by norm_num : (0 : ℝ) ≤ 4)
      have secondBound := mul_le_mul_of_nonneg_right scaled (sq_nonneg length)
      exact firstBound.trans (by convert secondBound using 1 <;> dsimp only [first, length] <;> ring)
    exact normalized.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right referenceSmall.le (sq_nonneg length))
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have blockAlignment (motion : PatchMotion count)
      (bounds : ∀ patch : Fin 4, ‖(patchCentroid motion time receiver patch - quadrupoleCenter motion time source) - ideal‖ ≤ 3 * gap / 16) :
      ‖(quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) - ideal‖ ≤ 3 * gap / 16 := by
    have identity : (quadrupoleCenter motion time receiver - quadrupoleCenter motion time source) - ideal =
        (∑ patch : Fin 4, ((patchCentroid motion time receiver patch - quadrupoleCenter motion time source) - ideal)) / 4 := by
      simp only [quadrupoleCenter, Fin.sum_univ_four]; ring
    rw [identity, norm_div]
    have summed := (norm_sum_le _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => bounds patch))
    norm_num at summed ⊢
    linarith only [summed]
  have firstAlignment := blockAlignment first (fun patch =>
    (alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside (receiver, patch) source different).1)
  have secondAlignment := blockAlignment second (fun patch =>
    (alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside (receiver, patch) source different).2.1)
  have combined : ‖(comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)‖ ≤ gap := by
    have identity : (comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter) =
        ((quadrupoleCenter first time receiver - firstCenter) - ideal) -
          ((quadrupoleCenter second time receiver - secondCenter) - ideal) := by dsimp only [comparison]; abel
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith only [firstAlignment, secondAlignment, gapPositive])
  have translationIdentity : changed.location (source.val + 1) * translation = ‖firstCenter - secondCenter‖ :=
    mul_div_cancel₀ _ sourcePositive.ne'
  have combinedSplit : ‖(comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)‖ ≤
      observer + changed.location (source.val + 1) * translation := by
    rw [translationIdentity]
    have identity : (comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter) =
        (quadrupoleCenter first time receiver - quadrupoleCenter second time receiver) - (firstCenter - secondCenter) := by
      dsimp only [comparison]; abel
    rw [identity]
    exact norm_sub_le _ _
  have separated (patch : Fin 4) : gap / 8 ≤
      ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center time‖ := by
    have normIdeal : ‖ideal‖ = gap := by dsimp only [ideal, gap]; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have firstTriangle := norm_sub_norm_le ideal (quadrupoleCenter second time receiver - secondCenter)
    rw [normIdeal, norm_sub_rev ideal] at firstTriangle
    have secondTriangle := norm_sub_norm_le (quadrupoleCenter second time receiver - secondCenter)
      ((comparison.second.patch patch).center time - secondCenter)
    rw [sub_sub_sub_cancel_right] at secondTriangle
    change gap / 8 ≤ ‖quadrupoleCenter second time receiver - (comparison.second.patch patch).center time‖
    linarith only [firstTriangle, secondTriangle, secondAlignment, (sourcePositions patch).2, lengthSmall, sourceGap, gapPositive]
  have centeredNonnegative : 0 ≤ centered := div_nonneg (norm_nonneg _) lengthPositive.le
  have rawNonnegative : 0 ≤ raw := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have spectralIdentity (patch : Fin 4) : (comparison.source patch).spectralDifferenceBudget = prepared.rawSourceShapeBudget time source patch := by
    with_reducible_and_instances
      dsimp only [comparison, original, MovingPatchFamilySourceComparison.quadrupole,
        FiniteMovingPatchFamily.quadrupoleSubfamily, MovingPatchFamilySourceComparison.source,
        MovingPatchSourceComparison.spectralDifferenceBudget, CascadeSourcePreparedPair.sourceComparison,
        CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate]
  have spectral (patch : Fin 4) : (comparison.source patch).spectralDifferenceBudget ≤ raw := by
    rw [spectralIdentity]
    exact Finset.single_le_sum (fun other _ => by dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity) (Finset.mem_univ patch)
  have displacements (patch : Fin 4) : ‖(comparison.source patch).displacementDifference‖ ≤
      observer + changed.location (source.val + 1) * translation + 4 * length * centered := by
    have component := (Finset.single_le_sum (fun other (_ : other ∈ (Finset.univ : Finset (Fin 4))) =>
      norm_nonneg (((comparison.first.patch other).center time - firstCenter) - ((comparison.second.patch other).center time - secondCenter)))
      (Finset.mem_univ patch)).trans positionDifference
    have identity : (comparison.source patch).displacementDifference =
        ((comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)) -
          (((comparison.first.patch patch).center time - firstCenter) - ((comparison.second.patch patch).center time - secondCenter)) := by
      change (comparison.firstReceiver time - (comparison.first.patch patch).center time) -
        (comparison.secondReceiver time - (comparison.second.patch patch).center time) = _
      abel
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith only [combinedSplit, component])
  have ratioSmall : 8 * 96 * comparison.receiverRadius / (gap / 8) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < gap / 8)).mpr
    have radiusBound : radius ≤ changed.location (receiver.val + 1) / (100000 * 96) := radiusSmall
    change 8 * 96 * radius ≤ _
    linarith only [radiusBound, receiverGap, gapPositive]
  have bound := incoming_comparison_bound comparison firstCenter secondCenter
    (changed.circulation_pos frequencyPositive ratioPositive _).le baseNonnegative gapPositive sourcePositive lengthPositive
    gapOne (changed.location_le_one _) gapReceiver sourceGap lengthGap centeredNonnegative (norm_nonneg _)
    (div_nonneg (norm_nonneg _) sourcePositive.le) rawNonnegative (norm_nonneg _) ratioSmall momentDifference.le referenceMoment
    positionDifference positions combined combinedSplit
    (fun patch => prepared.sourceComparison_quadrupole_mass_budget path fullInside (finProdFinEquiv (receiver, 0)) shapes
      amplitudePositive frequencyPositive ratioPositive source patch)
    (fun patch => by
      have identity : (comparison.source patch).first.radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source patch
      rw [identity]; exact physicalSmall)
    separated displacements spectral
  dsimp only at seriesActual
  have finalBound := seriesActual.2.trans bound
  change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(prepared.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter second current receiver) radius (power + 1) time -
        (prepared.referenceWitness.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter first current receiver) radius (power + 1) time‖) ∧ _
  constructor
  · simpa only [norm_sub_rev] using seriesActual.1
  · simpa only [translation, observer, raw, centered, moment, first, second, firstCenter, secondCenter, changed, norm_sub_rev] using finalBound

end EulerNonuniqueness.Paper
