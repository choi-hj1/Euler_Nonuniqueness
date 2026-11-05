import EulerNonuniqueness.Section5.CascadeRawSourceWeightedHistory
import EulerNonuniqueness.Section5.CascadeCanonicalBoundarySourceReturn
import EulerNonuniqueness.Section3.MovingMaterialCentroidRegularity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.Section6 FiniteMovingPatchFamily

namespace CascadeSourcePreparedPair

variable {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

def rawSourceShapeBudget
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (time : ℝ) (index : Fin count) (patch : Fin 4) : ℝ :=
  let first := prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time
  let final := prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time
  ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
    (‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) *
      ‖diskNeutralCLM first - diskNeutralCLM final‖

def rawSourceCenteredState
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (time : ℝ) (index : Fin count) : ℝ :=
  ‖(fun patch => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
      quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index) -
    (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)‖ / scales.length (index.val + 1)

end CascadeSourcePreparedPair

private theorem weighted_four_feedback_absorb
    {raw coefficients : Fin 4 → ℝ → ℝ} {center macroEnvelope : ℝ → ℝ}
    {finish weight omega epsilon history own foreign : ℝ}
    (finishNonnegative : 0 ≤ finish) (omegaPositive : 0 < omega) (weightBound : omega ≤ weight)
    (historyNonnegative : 0 ≤ history) (ownNonnegative : 0 ≤ own) (foreignNonnegative : 0 ≤ foreign)
    (rawContinuous : ∀ patch, ContinuousOn (raw patch) (Icc 0 finish))
    (coefficientContinuous : ∀ patch, ContinuousOn (coefficients patch) (Icc 0 finish))
    (centerContinuous : ContinuousOn center (Icc 0 finish)) (macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish))
    (rawNonnegative : ∀ patch time, 0 ≤ raw patch time)
    (historyBound : ∀ patch, weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw patch time) ≤
      history * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coefficients patch time)
    (coefficientBound : ∀ patch, ∀ time ∈ Icc 0 finish,
      coefficients patch time ≤ own * omega * (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign * macroEnvelope time)
    (small : 4 * history * own * epsilon ≤ 1 / 2) :
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ∑ patch : Fin 4, raw patch time) ≤
      8 * history * own * omega * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        8 * history * foreign * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * macroEnvelope time) := by
  let weighted := fun value : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * value time
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have rawSumContinuous : ContinuousOn (fun time => ∑ patch : Fin 4, raw patch time) (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ => rawContinuous patch)
  have rawIntegrable (patch : Fin 4) := (weightContinuous.continuousOn.mul (rawContinuous patch)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have sumIdentity : weighted (fun time => ∑ patch : Fin 4, raw patch time) = ∑ patch : Fin 4, weighted (raw patch) := by
    dsimp only [weighted]
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => rawIntegrable patch)
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => historyBound patch)
  rw [← Finset.mul_sum, ← sumIdentity] at summed
  have individual (patch : Fin 4) : weighted (coefficients patch) ≤
      own * omega * (weighted center + epsilon * weighted (fun time => ∑ other : Fin 4, raw other time)) + foreign * weighted macroEnvelope := by
    have upperContinuous : ContinuousOn (fun time => own * omega *
        (center time + epsilon * ∑ other : Fin 4, raw other time)) (Icc 0 finish) :=
      continuousOn_const.mul (centerContinuous.add (continuousOn_const.mul rawSumContinuous))
    have upper : ContinuousOn (fun time => own * omega *
        (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign * macroEnvelope time) (Icc 0 finish) :=
      upperContinuous.add (continuousOn_const.mul macroContinuous)
    have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative
      ((weightContinuous.continuousOn.mul (coefficientContinuous patch)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
      ((weightContinuous.continuousOn.mul upper).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
      (fun time inside => mul_le_mul_of_nonneg_left (coefficientBound patch time inside) (Real.exp_pos _).le)
    have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (own * omega * (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign * macroEnvelope time)) =
        own * omega * (weighted center + epsilon * weighted (fun time => ∑ other : Fin 4, raw other time)) + foreign * weighted macroEnvelope := by
      simp_rw [mul_add, mul_left_comm (Real.exp _) (own * omega), mul_left_comm (Real.exp _) foreign,
        mul_left_comm (Real.exp _) epsilon]
      have centerIntegrable := (weightContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
      have rawIntegrable := (weightContinuous.continuousOn.mul rawSumContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
      have macroIntegrable := (weightContinuous.continuousOn.mul macroContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
      rw [intervalIntegral.integral_add
          ((centerIntegrable.const_mul (own * omega)).add ((rawIntegrable.const_mul epsilon).const_mul (own * omega)))
          (macroIntegrable.const_mul foreign),
        intervalIntegral.integral_add (centerIntegrable.const_mul (own * omega))
          ((rawIntegrable.const_mul epsilon).const_mul (own * omega))]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    exact comparison.trans_eq identity
  have coefficientSum := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
    mul_le_mul_of_nonneg_left (individual patch) historyNonnegative)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at coefficientSum
  have rawIntegralNonnegative : 0 ≤ weighted (fun time => ∑ patch : Fin 4, raw patch time) :=
    intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun patch _ => rawNonnegative patch time))
  have absorption := mul_le_mul_of_nonneg_right small rawIntegralNonnegative
  have weightComparison := mul_le_mul_of_nonneg_right weightBound rawIntegralNonnegative
  have omegaAbsorption := mul_le_mul_of_nonneg_left absorption omegaPositive.le
  change weight * weighted (fun time => ∑ patch : Fin 4, raw patch time) ≤ _
  nlinarith [summed.trans coefficientSum]

theorem exists_uniform_actual_raw_source_weighted_feedback :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      ∀ weight : ℝ, ({scales with frequency := frequency}).omega (index.val + 1) ≤ weight →
      let changed : Scales := {scales with frequency := frequency}
      weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤
      constant * changed.omega (index.val + 1) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      (constant / changed.location (index.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖) := by
  obtain ⟨historyCap, historyPositive, histories⟩ := exists_uniform_actual_raw_source_weighted_history
  obtain ⟨canonicalCap, canonicalPositive, foreign, foreignNonnegative, canonical⟩ := exists_uniform_actual_canonical_boundary_source_return
  obtain ⟨continuityCap, continuityPositive, rawContinuity⟩ := exists_uniform_actual_raw_spectral_continuity
  let rawCap := min historyCap (min canonicalCap continuityCap)
  have capPositive : 0 < rawCap := lt_min historyPositive (lt_min canonicalPositive continuityPositive)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨history, historyOne, historyRoot, historyEight, historyParameters⟩ := histories factor factorPositive factorSmall
  obtain ⟨own, ownNonnegative, canonicalParameters⟩ := canonical factorPositive factorSmall
  obtain ⟨continuityRoot, continuityEight, coefficientParameters⟩ :=
    exists_uniform_actual_canonical_boundary_coefficient_continuity factor factorPositive factorSmall
  let constant := 8 * history * (own + foreign + 1)
  let rootMin := max historyRoot continuityRoot
  refine ⟨constant, by dsimp only [constant]; positivity, rootMin, historyEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootEight : 8 ≤ scaleRoot := (historyEight.trans (le_max_left _ _)).trans rootLarge
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  let tolerance := Real.sqrt (1 / (8 * history * (own + 1)))
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  filter_upwards [historyParameters scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    canonicalParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      (scaleRoot := scaleRoot) (boundaryConstant := boundaryConstant) thresholdSmall referenceNonnegative
      (by linarith) boundaryOne,
    coefficientParameters scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith) tolerancePositive,
    eventually_gt_atTop (0 : ℝ)] with frequency weightedHistory canonicalBound coefficientContinuity radiusSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index finish finishNonnegative finishBound weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let raw := fun patch time => prepared.rawSourceShapeBudget time index patch
  let center := fun time => prepared.rawSourceCenteredState time index
  let macroEnvelope := fun time => ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  let coefficients := fun patch => canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily
    prepared.trajectory.movingFamily (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch))
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let row := 216360000 * changed.hessian + 576 * changed.strain
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have omegaPositive : 0 < changed.omega (index.val + 1) := changed.omega_pos frequencyPositive (by dsimp only [changed]; linarith) _
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
  have rawNonnegative (patch : Fin 4) (time : ℝ) : 0 ≤ raw patch time := by
    dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have rawContinuousAll (source : Fin count) (patch : Fin 4) :
      ContinuousOn (fun time => prepared.rawSourceShapeBudget time source patch) (Icc 0 finish) := by
    obtain ⟨first, final⟩ := rawContinuity prepared capPositive
      ((min_le_right historyCap _).trans (min_le_right canonicalCap continuityCap)) path (finProdFinEquiv (source, patch))
    have firstProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskPhysicalTransverseProjection.continuous.comp_continuousOn (first.mono subset)
    have finalProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskPhysicalTransverseProjection.continuous.comp_continuousOn (final.mono subset)
    have firstNeutral : ContinuousOn (fun time => diskNeutralCLM
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskNeutralCLM.continuous.comp_continuousOn (first.mono subset)
    have finalNeutral : ContinuousOn (fun time => diskNeutralCLM
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskNeutralCLM.continuous.comp_continuousOn (final.mono subset)
    unfold CascadeSourcePreparedPair.rawSourceShapeBudget
    with_reducible_and_instances
      exact (firstProjection.sub finalProjection).norm.add
        ((firstProjection.norm.add finalProjection.norm).mul (firstNeutral.sub finalNeutral).norm)
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  have centroidContinuous (family : FiniteMovingPatchFamily (count * 4))
      (interior : ∀ label, Icc (0 : ℝ) finish ⊆ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (source : Fin count) (patch : Fin 4) :
      ContinuousOn (fun time => patchCentroid family.patchMotion time source patch) (Icc 0 finish) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact fun time inside => ((family.patch _).centroid_contDiffAt (interior _ inside)).continuousAt.continuousWithinAt
  have firstInterior (label : Fin (count * 4)) : Icc (0 : ℝ) finish ⊆ Ioo (first.patch label).initialTime (first.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have finalInterior (label : Fin (count * 4)) : Icc (0 : ℝ) finish ⊆ Ioo (final.patch label).initialTime (final.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have firstCenter (source : Fin count) : ContinuousOn (fun time => quadrupoleCenter first.patchMotion time source) (Icc 0 finish) :=
    (continuousOn_finset_sum _ (fun patch _ => centroidContinuous first firstInterior source patch)).div_const 4
  have finalCenter (source : Fin count) : ContinuousOn (fun time => quadrupoleCenter final.patchMotion time source) (Icc 0 finish) :=
    (continuousOn_finset_sum _ (fun patch _ => centroidContinuous final finalInterior source patch)).div_const 4
  have centeredContinuous (source : Fin count) : ContinuousOn (fun time =>
      (fun patch => patchCentroid first.patchMotion time source patch - quadrupoleCenter first.patchMotion time source) -
      (fun patch => patchCentroid final.patchMotion time source patch - quadrupoleCenter final.patchMotion time source)) (Icc 0 finish) :=
    continuousOn_pi.mpr fun patch =>
      ((centroidContinuous first firstInterior source patch).sub (firstCenter source)).sub
        ((centroidContinuous final finalInterior source patch).sub (finalCenter source))
  have centerContinuous : ContinuousOn center (Icc 0 finish) := (centeredContinuous index).norm.div_const _
  have macroStateContinuous (source : Fin count) : ContinuousOn (fun time => prepared.macroSourceState time source) (Icc 0 finish) := by
    have gaugeContinuous (family : FiniteMovingPatchFamily (count * 4)) (patch : Fin 4) :
        ContinuousOn (fun time => family.cascadeCenters time (source, patch)) (Icc 0 finish) :=
      fun time _ => ((family.patch _).center_equation time).continuousAt.continuousWithinAt
    have centeredSum := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
      (((gaugeContinuous first patch).sub (firstCenter source)).sub
        ((gaugeContinuous final patch).sub (finalCenter source))).norm)
    have rawSum := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => rawContinuousAll source patch)
    have identity : (fun time => prepared.macroSourceState time source) = fun time =>
        (‖quadrupoleCenter first.patchMotion time source - quadrupoleCenter final.patchMotion time source‖ +
          ∑ patch : Fin 4, ‖(first.cascadeCenters time (source, patch) - quadrupoleCenter first.patchMotion time source) -
            (final.cascadeCenters time (source, patch) - quadrupoleCenter final.patchMotion time source)‖) /
          changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
      funext time
      with_reducible_and_instances
        dsimp only [CascadeSourcePreparedPair.macroSourceState, CascadeSourcePreparedPair.rawSourceShapeBudget,
          MovingCentroidGaugeTrajectory.spectralCoordinate, first, final, changed]
    rw [identity]
    exact ((((firstCenter source).sub (finalCenter source)).norm.add centeredSum).div_const
      (changed.location (source.val + 1))).add rawSum
  have macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr fun source => continuousOn_const.mul (macroStateContinuous source)).norm
  have coefficientContinuous (patch : Fin 4) : ContinuousOn (coefficients patch) (Icc 0 finish) :=
    (coefficientContinuity count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).mono subset
  have histories (patch : Fin 4) : weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw patch time) ≤
      history * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coefficients patch time := by
    have actual := weightedHistory count orbit sectionTime phase dipoleAngle prepared capPositive (min_le_left _ _) path index patch
      finish finishNonnegative finishBound weight weightPositive
    with_reducible_and_instances
      dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget, coefficients] at actual ⊢
      exact actual
  have rowNonnegative : 0 ≤ row := by
    have strain : 0 ≤ changed.strain := tsum_nonneg fun index => div_nonneg
      (changed.circulation_pos frequencyPositive (by dsimp only [changed]; linarith) _).le (sq_nonneg _)
    have hessian : 0 ≤ changed.hessian := tsum_nonneg fun index => div_nonneg
      (changed.circulation_pos frequencyPositive (by dsimp only [changed]; linarith) _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [row]
    positivity
  have pointwise (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      coefficients patch time ≤ own * changed.omega (index.val + 1) * (center time + epsilon * ∑ other : Fin 4, raw other time) +
        ((foreign / changed.location (index.val + 1) ^ 4) * row) * macroEnvelope time := by
    let enlarged := prepared.enlargeCap ((min_le_right historyCap _).trans (min_le_left canonicalCap continuityCap))
    have actual := (canonicalBound count phase dipoleAngle enlarged path (subset inside) (index, patch)).2
    have normalized : coefficients patch time ≤ own * changed.omega (index.val + 1) *
        (center time + epsilon * ∑ other ∈ Finset.univ.erase patch, raw other time) +
          ((foreign / changed.location (index.val + 1) ^ 4) * row) * macroEnvelope time := by
      with_reducible_and_instances
        dsimp only [coefficients, center, raw, epsilon, row, macroEnvelope,
          CascadeSourcePreparedPair.rawSourceShapeBudget, CascadeSourcePreparedPair.rawSourceCenteredState,
          CascadeSourcePreparedPair.macroSourceState, MovingCentroidGaugeTrajectory.spectralCoordinate,
          enlarged, CascadeSourcePreparedPair.enlargeCap] at actual ⊢
        exact actual
    apply normalized.trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg ownNonnegative omegaPositive.le)
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun other _ _ => rawNonnegative other time))
      (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have small : 4 * history * own * epsilon ≤ 1 / 2 := by
    have radiusBound := (radiusSmall (index.val + 1)).le
    have lengthPositive := changed.length_pos (index.val + 1)
    have radiusNonnegative := (changed.radius_pos amplitudePositive frequencyPositive (by dsimp only [changed]; linarith) (index.val + 1)).le
    have squared := pow_le_pow_left₀ radiusNonnegative radiusBound 2
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 / (8 * history * (own + 1)))] at squared
    have epsilonBound : epsilon ≤ 1 / (8 * history * (own + 1)) := (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr squared
    have denominator : 0 < 8 * history * (own + 1) := by positivity
    have normalized := (le_div_iff₀ denominator).mp epsilonBound
    have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have actual := weighted_four_feedback_absorb finishNonnegative
    (changed.omega_pos frequencyPositive (by dsimp only [changed]; linarith) _) weightBound
    (zero_le_one.trans historyOne) ownNonnegative
    (mul_nonneg (div_nonneg foreignNonnegative (pow_nonneg (changed.location_pos _).le _)) rowNonnegative)
    (rawContinuousAll index) coefficientContinuous centerContinuous macroContinuous rawNonnegative histories pointwise small
  have centerIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time :=
    intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le
      (div_nonneg (norm_nonneg _) (changed.length_pos _).le))
  have macroIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * macroEnvelope time :=
    intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  apply actual.trans
  apply add_le_add
  · have coefficientBound : 8 * history * own ≤ constant := by dsimp only [constant]; nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right coefficientBound omegaPositive.le) centerIntegralNonnegative
  · have coefficientBound : 8 * history * foreign ≤ constant := by dsimp only [constant]; nlinarith
    have comparison := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right coefficientBound
        (pow_nonneg (changed.location_pos (index.val + 1)).le 4)) rowNonnegative) macroIntegralNonnegative
    convert comparison using 1 <;> ring

end EulerNonuniqueness.Paper
