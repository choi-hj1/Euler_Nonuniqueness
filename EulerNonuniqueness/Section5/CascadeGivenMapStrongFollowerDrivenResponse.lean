import EulerNonuniqueness.Section5.CascadeGivenMapCoarseSourceResponse
import EulerNonuniqueness.Section5.CascadeFollowerDrivenEnvelopeVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_given_map_strong_follower_driven_response
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∃ comparisonConstant ≥ (1 : ℝ), ∃ geometryConstant ≥ (1 : ℝ),
    ∃ rowConstant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (2 * constant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
      (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
      (∀ receiver : Fin count, receiver.val < drive.val → ∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
            Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
      let changed : Scales := {scales with frequency := frequency}
      let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then
        changed.location (receiver.val + 1) ^ 4 *
          (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) else 0‖
      let driver := fun time => prepared.weightedMacroSourceState time drive
      let remaining := prepared.followerStrictlyFinerForcing drive
      let rho := 216360000 * changed.hessian + 576 * changed.strain
      let growth := constant * changed.omega (drive.val + 1) / changed.ratio
      let multiplier := comparisonConstant * constant
      let feedback := rowConstant * geometryConstant * rho
      ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧
      ContinuousOn remaining (Icc 0 finish) ∧ IntervalIntegrable envelope volume 0 finish ∧
      IntervalIntegrable driver volume 0 finish ∧ IntervalIntegrable remaining volume 0 finish ∧
      envelope 0 = 0 ∧ ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp (growth * (time - current)) *
          (rowConstant * rho * (geometryConstant * envelope current + driver current) + remaining current)) volume 0 time ∧
        IntervalIntegrable (fun current => Real.exp ((growth + multiplier * feedback) * (time - current)) *
          (rowConstant * rho * driver current + remaining current)) volume 0 time ∧
        envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time,
          Real.exp (growth * (time - current)) *
            (rowConstant * rho * (geometryConstant * envelope current + driver current) + remaining current) ∧
        envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time,
          Real.exp ((growth + multiplier * feedback) * (time - current)) *
            (rowConstant * rho * driver current + remaining current) := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, sourceCap, sourcePositive, sourceFactory⟩ :=
    exists_uniform_actual_given_map_coarse_source_response graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨rowCap, rowPositive, rowConstant, rowNonnegative, rowFactory⟩ := exists_uniform_actual_follower_forcing_row
  obtain ⟨partitionCap, partitionPositive, partitionFactory⟩ := exists_uniform_actual_foreign_forcing_partition
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min sourceCap (min rowCap (min partitionCap continuityCap))
  have rawPositive : 0 < rawCap := lt_min sourcePositive (lt_min rowPositive (lt_min partitionPositive continuityPositive))
  have sourceCapBound : rawCap ≤ sourceCap := min_le_left _ _
  have rowCapBound : rawCap ≤ rowCap := (min_le_right _ _).trans (min_le_left _ _)
  have partitionCapBound : rawCap ≤ partitionCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have continuityCapBound : rawCap ≤ continuityCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨sourceRadius, sourcePositiveRadius, sourceQuarter, constant, constantOne, comparisonConstant,
    comparisonOne, rootMin, rootEight, sources⟩ := sourceFactory factorPositive factorSmall
  let radius := min sourceRadius geometryRadius
  let multiplier := comparisonConstant * constant
  have multiplierNonnegative : 0 ≤ multiplier := mul_nonneg (zero_le_one.trans comparisonOne) (zero_le_one.trans constantOne)
  have geometryNonnegative : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  refine ⟨radius, lt_min sourcePositiveRadius geometryPositive, (min_le_left _ _).trans sourceQuarter,
    constant, constantOne, comparisonConstant, comparisonOne, geometryConstant, geometryOne,
    rowConstant, rowNonnegative, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [sources scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    rowFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    partitionFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (1 : ℝ)]
    with frequency sourceEstimate geometryEstimate coherence rowEstimate partitionEstimate selectedContinuous frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive driveNonterminal finish finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  let nextDrive : Fin count := ⟨drive.val + 1, driveNonterminal⟩
  let followers := Finset.univ.filter (fun receiver : Fin count => receiver.val < drive.val)
  let external := fun receiver : Fin count => Finset.univ.filter
    (fun source : Fin count => drive.val < source.val ∧ source ≠ receiver)
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let growth := constant * changed.omega (drive.val + 1) / changed.ratio
  let feedback := rowConstant * geometryConstant * rho
  let fullForcing := fun receiver time => prepared.finiteCoordinateForeignForcing receiver time +
    prepared.physicalForeignSourceForcing receiver time
  let inputs := fun receiver time => changed.location (receiver.val + 1) ^ 4 * fullForcing receiver time
  have rawCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) (chosen : Fin 2 → ℝ → ℝ) :
      (prepared.enlargeCap bound).finiteCoordinateSize graph coordinate chosen =
        prepared.finiteCoordinateSize graph coordinate chosen := rfl
  have macroCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have selectedCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have forcingCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have envelopeCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext currentDrive current
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState, macroCapInvariant]
  have sourceChoice (receiver : Fin count) : ∃ chosen : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (chosen side) ∧ chosen side 0 = phase (receiver.val + 1)) ∧
      (receiver.val < drive.val →
        (∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
              Complex.exp (Complex.I * (chosen side time : ℂ))) ∧
        ContinuousOn (prepared.finiteCoordinateSize graph coordinate chosen receiver) (Icc 0 finish) ∧
        ContinuousOn (fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) (Icc 0 finish) ∧
        ContinuousOn (fullForcing receiver) (Icc 0 finish) ∧
        ∀ time ∈ Icc 0 finish,
          prepared.finiteCoordinateSize graph coordinate chosen receiver time +
            (∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) ≤ multiplier * ∫ current in (0 : ℝ)..time,
              Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current) := by
    by_cases below : receiver.val < drive.val
    · have nonterminal : receiver.val + 1 < count := by omega
      obtain ⟨chosen, properties, polar, actual⟩ := sourceEstimate count phase dipoleAngle
        (prepared.enlargeCap sourceCapBound) path receiver nonterminal finish finishNonnegative finishBound
          (fun time inside => (small receiver below time inside).trans (min_le_left _ _))
      dsimp only at actual
      simp only [sizeCapInvariant, rawCapInvariant, forcingCapInvariant, physicalCapInvariant] at actual
      obtain ⟨sizeContinuous, rawContinuous, forcingContinuous, physicalContinuous, _, _, _, _, _, response⟩ := actual
      exact ⟨chosen, properties, fun _ => ⟨polar, sizeContinuous, rawContinuous,
        forcingContinuous.add physicalContinuous, fun time inside => (response time inside).2⟩⟩
    · exact ⟨fun _ _ => phase (receiver.val + 1), fun _ => ⟨continuous_const, rfl⟩, fun impossible => (below impossible).elim⟩
  choose lift liftProperties liftData using sourceChoice
  let size := fun receiver => prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver
  let raw := fun receiver time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
  let states := fun receiver time => changed.location (receiver.val + 1) ^ 4 * (size receiver time + raw receiver time)
  let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then states receiver time else 0‖
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have macroBound (receiver : Fin count) (below : receiver.val < drive.val) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.macroSourceState time receiver ≤ geometryConstant * (size receiver time + raw receiver time) := by
    have nonterminal : receiver.val + 1 < count := by omega
    obtain ⟨chosen, properties, polar, _, _, _, bounds⟩ := geometryEstimate prepared path receiver nonterminal finish
      finishNonnegative finishBound (fun current member => (small receiver below current member).trans (min_le_right _ _))
    have equality := (coherence prepared path receiver finish finishNonnegative finishBound
      (fun current member => (small receiver below current member).trans ((min_le_left _ _).trans sourceQuarter))
      chosen (lift receiver) (fun side => (properties side).1.continuousOn)
      (fun side => (liftProperties receiver side).1.continuousOn)
      (fun side => (properties side).2.trans (liftProperties receiver side).2.symm) polar (liftData receiver below).1).2.2 graph coordinate
    have actual := (bounds time inside).2
    rw [equality inside] at actual
    exact actual
  have stateNonnegative (receiver : Fin count) (time : ℝ) : 0 ≤ states receiver time := by
    have locationPositive := changed.location_pos (receiver.val + 1)
    have sizeNonnegative : 0 ≤ size receiver time := by
      dsimp only [size, CascadeSourcePreparedPair.finiteCoordinateSize]; positivity
    have rawNonnegative : 0 ≤ raw receiver time := by
      apply Finset.sum_nonneg; intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    exact mul_nonneg (pow_nonneg locationPositive.le 4) (add_nonneg sizeNonnegative rawNonnegative)
  have envelopeNonnegative (time : ℝ) : 0 ≤ envelope time := norm_nonneg _
  have driverNonnegative (time : ℝ) : 0 ≤ driver time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time drive)
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have envelopeContinuous : ContinuousOn envelope (Icc 0 finish) := by
    apply ContinuousOn.norm; apply continuousOn_pi.mpr; intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using continuousOn_const.mul
        ((liftData receiver below).2.1.add (liftData receiver below).2.2.1)
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
  have driverContinuous : ContinuousOn driver (Icc 0 finish) :=
    continuousOn_const.mul (((stateContinuity prepared rawPositive continuityCapBound path drive).2.2.2).mono subset)
  have externalSubset (receiver : Fin count) : external receiver ⊆ Finset.univ.erase receiver := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have externalIdentity (receiver : Fin count) :
      Finset.univ.filter (fun source : Fin count => nextDrive.val ≤ source.val ∧ source ≠ receiver) = external receiver := by
    ext source
    simp only [external, nextDrive, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have selectedData (receiver : Fin count) := selectedContinuous count phase dipoleAngle prepared path receiver
    (external receiver) (externalSubset receiver)
  have remainingContinuous : ContinuousOn remaining (Icc 0 finish) := by
    apply ContinuousOn.norm; apply continuousOn_pi.mpr; intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using
        (continuousOn_const.mul ((selectedData receiver).2.1.mono subset) : ContinuousOn
          (fun current => changed.location (receiver.val + 1) ^ 4 *
            prepared.selectedForeignForcing (external receiver) receiver current) (Icc 0 finish))
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]; positivity
  have feedbackNonnegative : 0 ≤ feedback := mul_nonneg (mul_nonneg rowNonnegative geometryNonnegative) rhoNonnegative
  have componentBound (receiver : Fin count) (below : receiver.val < drive.val) (time : ℝ) : states receiver time ≤ envelope time := by
    have actual := norm_le_pi_norm (fun current : Fin count => if current.val < drive.val then states current time else 0) receiver
    simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg (stateNonnegative receiver time)] using actual
  have macroEnvelopeBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.coarserFollowerEnvelope drive time ≤ geometryConstant * envelope time := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg geometryNonnegative (envelopeNonnegative time))).mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · have scaled := mul_le_mul_of_nonneg_left (macroBound receiver below time inside)
        (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
      have stateBound : prepared.weightedMacroSourceState time receiver ≤ geometryConstant * states receiver time := by
        convert scaled using 1; dsimp only [CascadeSourcePreparedPair.weightedMacroSourceState, states]; ring
      have nonnegative : 0 ≤ prepared.weightedMacroSourceState time receiver :=
        mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time receiver)
      simpa only [CascadeSourcePreparedPair.coarserFollowerEnvelope, below, ite_true, Real.norm_eq_abs, abs_of_nonneg nonnegative]
        using stateBound.trans (mul_le_mul_of_nonneg_left (componentBound receiver below time) geometryNonnegative)
    · simp only [below, ite_false, norm_zero]
      exact mul_nonneg geometryNonnegative (envelopeNonnegative time)
  have nextEnvelopeBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.coarserFollowerEnvelope nextDrive time ≤ geometryConstant * envelope time + driver time := by
    have actual := General.norm_prefix_with_receiver_nonnegative_le (prepared.weightedMacroSourceState time)
      (fun source => mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time source)) drive drive le_rfl
    have predicate (source : Fin count) : source.val < nextDrive.val ↔ source.val < drive.val ∨ source = drive := by
      change source.val < drive.val + 1 ↔ source.val < drive.val ∨ source = drive
      constructor
      · intro below
        by_cases strict : source.val < drive.val
        · exact Or.inl strict
        · exact Or.inr (Fin.ext (by omega))
      · rintro (strict | same)
        · omega
        · subst source; omega
    have prefixBound : prepared.coarserFollowerEnvelope nextDrive time ≤ prepared.coarserFollowerEnvelope drive time + driver time := by
      change ‖fun source : Fin count => if source.val < nextDrive.val then prepared.weightedMacroSourceState time source else 0‖ ≤ _
      simp only [predicate]
      simpa only [Fin.lt_iff_val_lt_val, ite_true, CascadeSourcePreparedPair.coarserFollowerEnvelope] using actual
    exact prefixBound.trans (add_le_add_right (macroEnvelopeBound time inside) _)
  have memberBelow (receiver : Fin count) (member : receiver ∈ followers) : receiver.val < drive.val := (Finset.mem_filter.mp member).2
  have inputsContinuous (receiver : Fin count) (member : receiver ∈ followers) : ContinuousOn (inputs receiver) (Icc 0 finish) :=
    continuousOn_const.mul (liftData receiver (memberBelow receiver member)).2.2.2.1
  have inputsBound (receiver : Fin count) (member : receiver ∈ followers) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      inputs receiver time ≤ rowConstant * rho * (geometryConstant * envelope time + driver time) + remaining time := by
    have below := memberBelow receiver member
    have belowNext : receiver.val < nextDrive.val := by change receiver.val < drive.val + 1; omega
    have different : receiver ≠ nextDrive := by intro same; have equalValues := congrArg Fin.val same; omega
    obtain ⟨_, _, partitionBound⟩ := partitionEstimate count phase dipoleAngle (prepared.enlargeCap partitionCapBound) path (subset inside) receiver nextDrive
    simp only [forcingCapInvariant, physicalCapInvariant, selectedCapInvariant, externalIdentity] at partitionBound
    obtain ⟨_, _, _, rowBound⟩ := rowEstimate count phase dipoleAngle (prepared.enlargeCap rowCapBound) path time (subset inside) receiver nextDrive belowNext.le
    simp only [selectedCapInvariant, envelopeCapInvariant, different, ite_false, add_zero] at rowBound
    have drivenBound := rowBound.trans (mul_le_mul_of_nonneg_left (nextEnvelopeBound time inside) (mul_nonneg rowNonnegative rhoNonnegative))
    have remainingComponent : changed.location (receiver.val + 1) ^ 4 *
        prepared.selectedForeignForcing (external receiver) receiver time ≤ remaining time := by
      have actual := norm_le_pi_norm (fun current : Fin count => if current.val < drive.val then
        changed.location (current.val + 1) ^ 4 * prepared.selectedForeignForcing (external current) current time else 0) receiver
      have nonnegative := mul_nonneg (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4) ((selectedData receiver).1 time)
      simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg nonnegative] using actual
    have scaled := mul_le_mul_of_nonneg_left partitionBound (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    apply scaled.trans
    rw [mul_add]
    exact add_le_add drivenBound remainingComponent
  let forcing := fun time => rowConstant * rho * (geometryConstant * envelope time + driver time) + remaining time
  let resolvedForcing := fun time => rowConstant * rho * driver time + remaining time
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) :=
    (continuousOn_const.mul ((continuousOn_const.mul envelopeContinuous).add driverContinuous)).add remainingContinuous
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time :=
    add_nonneg (mul_nonneg (mul_nonneg rowNonnegative rhoNonnegative)
      (add_nonneg (mul_nonneg geometryNonnegative (envelopeNonnegative time)) (driverNonnegative time))) (remainingNonnegative time)
  have resolvedContinuous : ContinuousOn resolvedForcing (Icc 0 finish) :=
    (continuousOn_const.mul driverContinuous).add remainingContinuous
  have propagator (receiver : Fin count) (member : receiver ∈ followers) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      states receiver time ≤ multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * inputs receiver current := by
    have actual := mul_le_mul_of_nonneg_left ((liftData receiver (memberBelow receiver member)).2.2.2.2 time inside)
      (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    have identity : (∫ current in (0 : ℝ)..time,
        Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * inputs receiver current) =
        changed.location (receiver.val + 1) ^ 4 * ∫ current in (0 : ℝ)..time,
          Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro current _
      dsimp only [inputs]; ring
    rw [identity]
    convert actual using 1; dsimp only [states]; ring
  have ratesBound (receiver : Fin count) (member : receiver ∈ followers) : constant * changed.omega (receiver.val + 1) ≤ growth :=
    (changed.coarse_follower_rate_gap constant frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound])
      (zero_le_one.trans constantOne) receiver.val drive.val (memberBelow receiver member)).2.1
  have masked := General.norm_masked_exponential_volterra_le followers inputsContinuous forcingContinuous multiplierNonnegative
    (fun receiver _ time _ => stateNonnegative receiver time) (fun time _ => forcingNonnegative time) ratesBound inputsBound propagator
  have preliminary (time : ℝ) (inside : time ∈ Icc 0 finish) :
      envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) * forcing current := by
    simpa only [followers, Finset.mem_filter, Finset.mem_univ, true_and] using masked time inside
  have initial : envelope 0 = 0 := by
    apply le_antisymm _ (envelopeNonnegative 0)
    simpa only [intervalIntegral.integral_same, mul_zero] using (preliminary 0 ⟨le_rfl, finishNonnegative⟩)
  have split : forcing = fun time => resolvedForcing time + feedback * envelope time := by
    funext time; dsimp only [forcing, resolvedForcing, feedback]; ring
  have resolved := exponential_volterra_gronwall (initial := 0) (rate := growth) (feedback := feedback) (multiplier := multiplier)
    envelopeContinuous resolvedContinuous feedbackNonnegative multiplierNonnegative finishNonnegative (by
      intro time inside
      have actual := preliminary time inside
      rw [split] at actual
      simpa only [zero_mul, zero_add] using actual)
  refine ⟨lift, liftProperties, fun receiver below => (liftData receiver below).1,
    envelopeContinuous, driverContinuous, remainingContinuous, envelopeContinuous.intervalIntegrable_of_Icc finishNonnegative,
    driverContinuous.intervalIntegrable_of_Icc finishNonnegative, remainingContinuous.intervalIntegrable_of_Icc finishNonnegative, initial, ?_⟩
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have originalKernel : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by fun_prop
  have resolvedKernel : Continuous (fun current : ℝ => Real.exp ((growth + multiplier * feedback) * (time - current))) := by fun_prop
  exact ⟨(originalKernel.continuousOn.mul (forcingContinuous.mono prefixSubset)).intervalIntegrable_of_Icc inside.1,
    (resolvedKernel.continuousOn.mul (resolvedContinuous.mono prefixSubset)).intervalIntegrable_of_Icc inside.1,
    preliminary time inside, by simpa only [zero_mul, zero_add] using resolved time inside⟩

end EulerNonuniqueness.Paper
