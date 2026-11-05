import EulerNonuniqueness.Section5.CascadeCoarserPatchCoefficientReturn
import EulerNonuniqueness.Section5.CascadeSelectedFinerExtentDiagonalFeedback
import EulerNonuniqueness.Section6.SourcePacketPairedPatchCommonEnvelope

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_mixed_foreign_patch_envelope :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count, ∀ completed : Finset (Fin count),
    ∀ outgoingStart initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source ∈ completed, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → source ∉ completed →
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
    let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let sharpState := fun source : Fin count => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let outgoingEnvelope := fun source : Fin count => changed.circulation (source.val + 1) *
      (4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
        ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
          changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)
    let foreign := fun patch power => (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch)
          ownRadius (power + 1) time‖
    (∀ patch : Fin 4, ∀ source ∈ Finset.univ.erase receiver,
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source)) ∧
    (∀ patch : Fin 4, Summable (foreign patch)) ∧
    (∑ patch : Fin 4, ∑' power : ℕ, foreign patch power) ≤
      coarseConstant / changed.location (receiver.val + 1) ^ 4 * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ +
      incomingConstant * extent ^ 2 * (∑ source ∈ finer.filter (fun source => source ∉ completed),
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * sharpState source) +
      8000000000 / changed.location (receiver.val + 1) ^ 4 * (∑ source ∈ finer.filter (fun source => source ∈ completed), outgoingEnvelope source) +
      tolerance * prepared.macroSourceState time receiver := by
  obtain ⟨coarseCap, coarsePositive, coarseConstant, coarseNonnegative, coarseFactory⟩ := exists_uniform_actual_coarser_patch_coefficient_return
  obtain ⟨incomingCap, incomingPositive, incomingConstant, incomingNonnegative, incomingFactory⟩ := exists_uniform_actual_extent_source_patch_return
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, outgoingFactory⟩ := exists_actual_paired_patch_common_envelope
  let rawCap := min coarseCap incomingCap
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, lt_min coarsePositive incomingPositive,
    4 * coarseConstant, by positivity, 4 * incomingConstant, by positivity, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [coarseFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime (thresholdBound.trans thresholdEighth)
      referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    incomingFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime (thresholdBound.trans thresholdEighth)
      referenceNonnegative rootOne boundaryOne factorPositive factorEighth,
    outgoingFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    scales.eventually_sharp_receiver_correction_row_small ratioBound alphaPositive (constant := 5 * incomingConstant) (extent := extent)
      (by positivity) tolerancePositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1), eventually_gt_atTop (0 : ℝ)]
    with frequency coarse incoming outgoing correctionSmall lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver completed outgoingStart initialDistance direction
  dsimp only
  intro outgoingEntry incomingExtent
  let changed : Scales := {scales with frequency := frequency}
  let location := changed.location (receiver.val + 1)
  let radius := factor / 39321600 * changed.length (receiver.val + 1)
  let gap := fun source : Fin count => |location - changed.location (source.val + 1)|
  let coarseSources := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let incomingSources := Finset.univ.filter (fun source : Fin count => receiver.val < source.val ∧ source ∉ completed)
  let outgoingSources := Finset.univ.filter (fun source : Fin count => receiver.val < source.val ∧ source ∈ completed)
  let term := fun patch source => prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source
  let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference source time‖ +
    ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source - quadrupoleCenter prepared.reference time source‖ /
      changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let base := fun source => changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
    (1 + location / changed.location (source.val + 1)) * state source
  let coefficient := fun source => changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 5
  let observation := fun patch : Fin 4 => ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch -
    patchCentroid prepared.reference time receiver patch‖
  let envelope := fun source : Fin count => changed.circulation (source.val + 1) *
    (4 * ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time source‖ + changed.length (source.val + 1) *
      ‖firstDipoleCenter prepared.trajectory.movingFamily.patchMotion time source - secondDipoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ +
      changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)
  let coarseNorm := ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖
  have locationPositive : 0 < location := changed.location_pos _
  have radiusNonnegative : 0 ≤ radius := mul_nonneg (by positivity) (changed.length_pos _).le
  have radiusSmall : radius ≤ location / (2 * (100000 * 96)) := by
    have lengthSmall : changed.length (receiver.val + 1) ≤ location := by simpa only [one_mul] using (lengths (receiver.val + 1)).le
    calc
      _ ≤ factor / 39321600 * location := mul_le_mul_of_nonneg_left lengthSmall (by positivity)
      _ ≤ (1 : ℝ) / 39321600 * location := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right factorOne (by norm_num)) locationPositive.le
      _ = location / 39321600 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left locationPositive.le (by norm_num) (by norm_num)
  have radiusAllowed : radius ≤ location / (100000 * 96) := by linarith only [radiusSmall, locationPositive]
  have macroInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have coarseData (patch : Fin 4) : (∀ source ∈ coarseSources, Summable (term patch source)) ∧
      (∑ source ∈ coarseSources, ∑' power, term patch source power) ≤
        coarseConstant / location ^ 4 * (216360000 * changed.hessian + 576 * changed.strain) * coarseNorm := by
    have actual := coarse count phase dipoleAngle (prepared.enlargeCap (min_le_left _ _)) path inside (receiver, patch) radius radiusNonnegative radiusAllowed
    dsimp only at actual
    rw [macroInvariant] at actual
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    exact actual
  have incomingData (patch : Fin 4) (source : Fin count) (member : source ∈ incomingSources) :
      Summable (term patch source) ∧ (∑' power, term patch source power) ≤
        incomingConstant * extent ^ 2 * (base source + coefficient source * observation patch) := by
    have actual := incoming count phase dipoleAngle (prepared.enlargeCap (min_le_right _ _)) path receiver source (Finset.mem_filter.mp member).2.1 patch time inside
      (incomingExtent source (Finset.mem_filter.mp member).2.1 (Finset.mem_filter.mp member).2.2).1
      (incomingExtent source (Finset.mem_filter.mp member).2.1 (Finset.mem_filter.mp member).2.2).2 radius radiusNonnegative
      radiusAllowed
    dsimp only at actual
    rw [centerInvariant, rawInvariant] at actual
    with_reducible_and_instances
      dsimp only [term, base, coefficient, observation, state, gap, CascadeSourcePreparedPair.coarserPatchCoefficientTerm,
        CascadeSourcePreparedPair.enlargeCap] at actual ⊢
    simpa only [prepared.referenceIdentity] using actual
  have outgoingData (patch : Fin 4) (source : Fin count) (member : source ∈ outgoingSources) :
      Summable (term patch source) ∧ (∑' power, term patch source power) ≤ 2000000000 / location ^ 4 * envelope source := by
    obtain ⟨startNonnegative, startBound, initialLarge, initialSmall, directionNorm, firstInitial, secondInitial, initialProjection, initialUpper⟩ :=
      outgoingEntry source (Finset.mem_filter.mp member).2.2 (Finset.mem_filter.mp member).2.1
    have sourceHalf := changed.location_le_half_of_lt (show receiver.val + 1 < source.val + 1 by have := (Finset.mem_filter.mp member).2.1; omega)
    have distanceLower : location / 2 ≤ gap source := by
      dsimp only [gap]; rw [abs_of_nonneg (by linarith only [sourceHalf, locationPositive])]; linarith only [sourceHalf]
    have actual := outgoing count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source (Finset.mem_filter.mp member).2.1 patch
      (outgoingStart source) (time - outgoingStart source) (initialDistance source) startNonnegative (sub_nonneg.mpr startBound)
      (by linarith only [inside.2]) initialLarge initialSmall (direction source) directionNorm firstInitial secondInitial initialProjection initialUpper
      radius radiusNonnegative (by change radius ≤ gap source / (100000 * 96); linarith only [radiusSmall, distanceLower])
      (time - outgoingStart source) ⟨sub_nonneg.mpr startBound, le_rfl⟩
    dsimp only at actual
    simp only [add_sub_cancel] at actual
    refine ⟨actual.1, ?_⟩
    have bound : location ^ 4 * (∑' power, term patch source power) ≤ 2000000000 * envelope source := by
      simpa only [term, CascadeSourcePreparedPair.coarserPatchCoefficientTerm, envelope, location, changed, mul_assoc] using actual.2.1
    calc
      _ ≤ (2000000000 * envelope source) / location ^ 4 := (le_div_iff₀ (pow_pos locationPositive 4)).mpr (by simpa only [mul_comm] using bound)
      _ = _ := by ring
  have partition (values : Fin count → ℝ) : (∑ source ∈ Finset.univ.erase receiver, values source) =
      (∑ source ∈ coarseSources, values source) + (∑ source ∈ incomingSources, values source) + ∑ source ∈ outgoingSources, values source := by
    have pointwise (source : Fin count) : (if source ≠ receiver then values source else 0) =
        (if source.val < receiver.val then values source else 0) +
        (if receiver.val < source.val ∧ source ∉ completed then values source else 0) +
        (if receiver.val < source.val ∧ source ∈ completed then values source else 0) := by
      by_cases lower : source.val < receiver.val
      · simp [lower, show ¬receiver.val < source.val by omega, show source ≠ receiver by intro equal; subst source; omega]
      · by_cases upper : receiver.val < source.val
        · by_cases done : source ∈ completed <;> simp [lower, upper, done, show source ≠ receiver by intro equal; subst source; omega]
        · have equal : source = receiver := Fin.ext (by omega); simp [equal]
    have erased : Finset.univ.filter (fun source : Fin count => source ≠ receiver) = Finset.univ.erase receiver := by ext source; simp [and_comm]
    have actual := congrArg (fun values : Fin count → ℝ => ∑ source, values source) (funext pointwise)
    simpa only [Finset.sum_add_distrib, ← Finset.sum_filter, erased] using actual
  have sourceSummable (patch : Fin 4) (source : Fin count) (member : source ∈ Finset.univ.erase receiver) : Summable (term patch source) := by
    by_cases lower : source.val < receiver.val
    · exact (coarseData patch).1 source (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lower⟩)
    · have upper : receiver.val < source.val := by
        have different : source.val ≠ receiver.val := fun equal => (Finset.mem_erase.mp member).1 (Fin.ext equal)
        omega
      by_cases done : source ∈ completed
      · exact (outgoingData patch source (Finset.mem_filter.mpr ⟨Finset.mem_univ _, upper, done⟩)).1
      · exact (incomingData patch source (Finset.mem_filter.mpr ⟨Finset.mem_univ _, upper, done⟩)).1
  have patchBound (patch : Fin 4) : (∑ source ∈ Finset.univ.erase receiver, ∑' power, term patch source power) ≤
      coarseConstant / location ^ 4 * (216360000 * changed.hessian + 576 * changed.strain) * coarseNorm +
      incomingConstant * extent ^ 2 * ((∑ source ∈ incomingSources, base source) + (∑ source ∈ incomingSources, coefficient source) * observation patch) +
      2000000000 / location ^ 4 * ∑ source ∈ outgoingSources, envelope source := by
    rw [partition]
    apply add_le_add
    · apply add_le_add (coarseData patch).2
      have actual := Finset.sum_le_sum (fun source member => (incomingData patch source member).2)
      simpa only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc] using actual
    · simpa only [← Finset.mul_sum] using Finset.sum_le_sum (fun source member => (outgoingData patch source member).2)
  have totalBound := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => patchBound patch)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, ← Finset.mul_sum] at totalBound
  have correctionNonnegative : 0 ≤ ∑ source ∈ incomingSources, coefficient source := Finset.sum_nonneg fun source _ =>
    div_nonneg (mul_nonneg (changed.circulation_pos frequencyPositive (by change 0 < scales.ratio; linarith only [ratioBound]) _).le (sq_nonneg _)) (pow_nonneg (abs_nonneg _) _)
  have observationBound : (∑ patch : Fin 4, observation patch) ≤ 5 * prepared.macroSourceState time receiver := by
    have actual := prepared.receiver_observation_le_five_location_macroSourceState path inside receiver
    have smaller : (∑ patch : Fin 4, observation patch) ≤ 5 * location * prepared.macroSourceState time receiver := by
      dsimp only [observation]; linarith only [actual, norm_nonneg (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver - quadrupoleCenter prepared.reference time receiver)]
    exact smaller.trans (mul_le_mul_of_nonneg_right (by nlinarith only [changed.location_le_one (receiver.val + 1)] : 5 * location ≤ 5) (prepared.macroSourceState_nonnegative time receiver))
  have feedbackSmall := correctionSmall count receiver incomingSources (by intro source member equal; have := (Finset.mem_filter.mp member).2.1; subst source; omega)
  have feedback : incomingConstant * extent ^ 2 * ((∑ source ∈ incomingSources, coefficient source) * ∑ patch : Fin 4, observation patch) ≤
      tolerance * prepared.macroSourceState time receiver := by
    have observed := mul_le_mul_of_nonneg_left observationBound (mul_nonneg (mul_nonneg incomingNonnegative (sq_nonneg extent)) correctionNonnegative)
    have small := mul_le_mul_of_nonneg_right feedbackSmall.le (prepared.macroSourceState_nonnegative time receiver)
    convert observed.trans (by convert small using 1; dsimp only [coefficient, gap, location]; ring) using 1
    ring
  have foreignBound (patch : Fin 4) := General.summable_weighted_norm_of_eq_add_finite_corrections (Finset.univ.erase receiver)
    (fun power : ℕ => (96 : ℝ) ^ (power + 1)) (fun _ => by positivity)
    (fun power => prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time)
    (fun _ => (0 : ℂ)) (fun source power =>
      (prepared.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time -
      (prepared.referenceWitness.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time)
    (by intro power; dsimp only; rw [prepared.trajectory.movingFamily.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, ← Finset.sum_sub_distrib, zero_add])
    (by simpa only [norm_zero, mul_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))) (sourceSummable patch)
  refine ⟨sourceSummable, fun patch => (foreignBound patch).1, ?_⟩
  have triangle := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => (foreignBound patch).2)
  simp only [norm_zero, mul_zero, tsum_zero, zero_add] at triangle
  have combined := triangle.trans totalBound
  have normalized : (∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) radius (power + 1) time‖) ≤
      (4 * coarseConstant) / location ^ 4 * (216360000 * changed.hessian + 576 * changed.strain) * coarseNorm +
      (4 * incomingConstant) * extent ^ 2 * (∑ source ∈ incomingSources, base source) +
      8000000000 / location ^ 4 * (∑ source ∈ outgoingSources, envelope source) +
      incomingConstant * extent ^ 2 * ((∑ source ∈ incomingSources, coefficient source) * ∑ patch : Fin 4, observation patch) := by
    convert combined using 1
    ring
  have final := normalized.trans (add_le_add_left feedback _)
  convert final using 1
  simp only [Finset.filter_filter, and_assoc]
  ring

end EulerNonuniqueness.Paper
