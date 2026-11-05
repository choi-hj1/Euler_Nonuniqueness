import EulerNonuniqueness.Section5.CascadeIncomingSingletonCommonEnvelope
import EulerNonuniqueness.Section5.CascadeOutgoingSingletonCommonEnvelope
import EulerNonuniqueness.Section5.CascadeFollowerCommonSourceEnvelope
import EulerNonuniqueness.Section1.IncomingDiagonalHessianRow

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_mixed_follower_common_envelope :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ drive : Fin count, ∀ completed : Finset (Fin count),
    ∀ outgoingStart initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source ∈ completed, drive.val < source.val →
      0 ≤ outgoingStart source ∧ outgoingStart source ≤ time ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (outgoingStart source) source -
        (changed.length (source.val + 1) : ℂ) * direction source‖ ≤ changed.length (source.val + 1) / 64 ∧
      ‖secondDipoleSeparation motion (outgoingStart source) source -
        (changed.length (source.val + 1) : ℂ) * (-direction source)‖ ≤ changed.length (source.val + 1) / 64 ∧
      (3 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (outgoingStart source) source -
          secondDipoleCenter motion (outgoingStart source) source)).re ∧
      ‖firstDipoleCenter motion (outgoingStart source) source - secondDipoleCenter motion (outgoingStart source) source‖ ≤
        (5 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source) →
    (∀ source : Fin count, drive.val < source.val → source ∉ completed →
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
    let sharpState := fun source : Fin count => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let outgoingEnvelope := fun source : Fin count => changed.circulation (source.val + 1) *
      (4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
        ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
          changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)
    prepared.followerStrictlyFinerForcing drive time ≤
      outgoingConstant * (∑ source ∈ finer.filter (fun source => source ∈ completed), outgoingEnvelope source) +
        incomingConstant * extent ^ 2 * (∑ source ∈ finer.filter (fun source => source ∉ completed),
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
            (1 + (changed.location (source.val + 1))⁻¹) * sharpState source) +
        tolerance * prepared.coarserFollowerEnvelope drive time := by
  obtain ⟨rawCap, capPositive, incomingConstant, incomingNonnegative, incomingFactory⟩ :=
    exists_uniform_actual_incoming_singleton_common_envelope
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, outgoingConstant, outgoingNonnegative, outgoingFactory⟩ :=
    exists_actual_outgoing_singleton_common_envelope
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (incomingConstant * extent ^ 2)
  simp only [mul_zero] at hessianLimit
  filter_upwards [incomingFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    outgoingFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_finite_incoming_diagonal_sum_le_hessian ratioBound alphaPositive,
    hessianLimit.eventually (eventually_lt_nhds tolerancePositive), eventually_gt_atTop (0 : ℝ)]
    with frequency incoming outgoing hessianRow hessianSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside drive completed outgoingStart initialDistance direction
  dsimp only
  intro outgoingEntry incomingExtent
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let completedSources := finer.filter (fun source => source ∈ completed)
  let incomingSources := finer.filter (fun source => source ∉ completed)
  let coarse := prepared.coarserFollowerEnvelope drive time
  let sharpState := fun source : Fin count => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let outgoingEnvelope := fun source : Fin count => changed.circulation (source.val + 1) *
    (4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
      ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
        changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)
  let incomingEnvelope := fun source : Fin count => changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
    (1 + (changed.location (source.val + 1))⁻¹) * sharpState source
  let diagonal := fun source : Fin count => incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) *
    changed.length (source.val + 1) ^ 2 / changed.location (source.val + 1) ^ 4
  let envelope := fun source : Fin count => if source ∈ completed then outgoingConstant * outgoingEnvelope source else
    incomingConstant * extent ^ 2 * incomingEnvelope source + diagonal source * coarse
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationPositive (source : Fin count) := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have coarseNonnegative : 0 ≤ coarse := norm_nonneg _
  have sharpNonnegative (source : Fin count) : 0 ≤ sharpState source := by
    have centered : 0 ≤ prepared.rawSourceCenteredState time source :=
      div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have raw (patch : Fin 4) : 0 ≤ prepared.rawSourceShapeBudget time source patch := by
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    exact add_nonneg (add_nonneg (add_nonneg centered (norm_nonneg _))
      (div_nonneg (norm_nonneg _) (changed.location_pos _).le)) (Finset.sum_nonneg (fun patch _ => raw patch))
  have outgoingNonnegativeSource (source : Fin count) : 0 ≤ outgoingEnvelope source := by
    have := circulationPositive source
    have := changed.length_pos (source.val + 1)
    dsimp only [outgoingEnvelope]
    positivity
  have incomingNonnegativeSource (source : Fin count) : 0 ≤ incomingEnvelope source := by
    have := circulationPositive source
    have := changed.location_pos (source.val + 1)
    have := sharpNonnegative source
    dsimp only [incomingEnvelope]
    positivity
  have diagonalNonnegative (source : Fin count) : 0 ≤ diagonal source := by
    have := circulationPositive source
    have := changed.location_pos (source.val + 1)
    dsimp only [diagonal]
    positivity
  have envelopeNonnegative (source : Fin count) : 0 ≤ envelope source := by
    dsimp only [envelope]
    split_ifs
    · exact mul_nonneg outgoingNonnegative (outgoingNonnegativeSource source)
    · exact add_nonneg (mul_nonneg (mul_nonneg incomingNonnegative (sq_nonneg extent)) (incomingNonnegativeSource source))
        (mul_nonneg (diagonalNonnegative source) coarseNonnegative)
  have receiverBound (receiver : Fin count) (below : receiver.val < drive.val) :
      prepared.weightedMacroSourceState time receiver ≤ coarse := by
    have actual := norm_le_pi_norm (fun current : Fin count =>
      if current.val < drive.val then prepared.weightedMacroSourceState time current else 0) receiver
    have nonnegative : 0 ≤ prepared.weightedMacroSourceState time receiver :=
      mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time receiver)
    simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg nonnegative] using actual
  have commonBound (receiver : Fin count) (below : receiver.val < drive.val) (source : Fin count)
      (finerSource : drive.val < source.val) :
      changed.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing {source} receiver time ≤ envelope source := by
    have ordered : receiver.val < source.val := below.trans finerSource
    by_cases done : source ∈ completed
    · obtain ⟨startNonnegative, startBound, initialLarge, initialSmall, directionNorm,
        firstInitial, secondInitial, initialProjection, initialUpper⟩ := outgoingEntry source done finerSource
      have elapsedNonnegative : 0 ≤ time - outgoingStart source := sub_nonneg.mpr startBound
      have endIdentity : outgoingStart source + (time - outgoingStart source) = time := by ring
      have actual := (outgoing count phase dipoleAngle prepared path receiver source ordered
        (outgoingStart source) (time - outgoingStart source) (initialDistance source) startNonnegative elapsedNonnegative
        (by rw [endIdentity]; exact inside.2) initialLarge initialSmall (direction source) directionNorm
        firstInitial secondInitial initialProjection initialUpper (time - outgoingStart source) ⟨elapsedNonnegative, le_rfl⟩).2.2.2
      simpa only [envelope, done, ite_true, endIdentity, outgoingEnvelope, mul_assoc] using actual
    · have extents := incomingExtent source finerSource done
      have actual := incoming count phase dipoleAngle prepared path time inside receiver source ordered extents.1 extents.2
      have normalized : changed.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing {source} receiver time ≤
          incomingConstant * extent ^ 2 * incomingEnvelope source + diagonal source * prepared.weightedMacroSourceState time receiver := by
        convert actual using 1
        dsimp only [incomingEnvelope, diagonal, sharpState, CascadeSourcePreparedPair.weightedMacroSourceState]
        ring
      simpa only [envelope, done, ite_false] using normalized.trans
        (add_le_add_left (mul_le_mul_of_nonneg_left (receiverBound receiver below) (diagonalNonnegative source)) _)
  have pointwise := prepared.followerStrictlyFinerForcing_le_common_source_envelope drive time envelope
    (fun source _ => envelopeNonnegative source) commonBound
  have diagonalSum : (∑ source ∈ incomingSources, diagonal source) ≤ tolerance := by
    calc
      _ = (incomingConstant * extent ^ 2) * (∑ source ∈ incomingSources,
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / changed.location (source.val + 1) ^ 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        dsimp only [diagonal]
        ring
      _ ≤ (incomingConstant * extent ^ 2) * changed.hessian := mul_le_mul_of_nonneg_left
        (hessianRow count incomingSources) (mul_nonneg incomingNonnegative (sq_nonneg extent))
      _ ≤ tolerance := hessianSmall.le
  have split : (∑ source ∈ finer, envelope source) =
      outgoingConstant * (∑ source ∈ completedSources, outgoingEnvelope source) +
        incomingConstant * extent ^ 2 * (∑ source ∈ incomingSources, incomingEnvelope source) +
          (∑ source ∈ incomingSources, diagonal source) * coarse := by
    dsimp only [envelope]
    rw [Finset.sum_ite, Finset.sum_add_distrib, Finset.sum_mul]
    simp only [Finset.mul_sum, completedSources, incomingSources]
    ring
  exact pointwise.trans (split.trans_le (add_le_add_left
    (mul_le_mul_of_nonneg_right diagonalSum coarseNonnegative) _))

end EulerNonuniqueness.Paper
