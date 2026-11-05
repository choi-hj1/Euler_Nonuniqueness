import EulerNonuniqueness.Section5.CascadeCoarseSourceResponse
import EulerNonuniqueness.Section5.CascadeFollowerEnvelopeVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_strong_follower_envelope_volterra :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
      ∃ geometryConstant ≥ (1 : ℝ), ∃ feedbackConstant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
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
      ∀ drive : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
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
        let remaining := prepared.followerRemainingForcing drive
        let rho := 216360000 * changed.hessian + 576 * changed.strain
        let growth := constant * changed.omega (drive.val + 1) / changed.ratio
        ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
        IntervalIntegrable envelope volume 0 finish ∧ IntervalIntegrable remaining volume 0 finish ∧
        envelope 0 = 0 ∧
        (∀ time ∈ Icc 0 finish, prepared.coarserFollowerEnvelope drive time ≤ geometryConstant * envelope time) ∧
        ∀ time ∈ Icc 0 finish,
          IntervalIntegrable (fun current => Real.exp (growth * (time - current)) *
            (feedbackConstant * rho * envelope current + remaining current)) volume 0 time ∧
          IntervalIntegrable (fun current => Real.exp ((growth + constant * (feedbackConstant * rho)) *
            (time - current)) * remaining current) volume 0 time ∧
          envelope time ≤ constant * ∫ current in (0 : ℝ)..time,
            Real.exp (growth * (time - current)) * (feedbackConstant * rho * envelope current + remaining current) ∧
          envelope time ≤ constant * ∫ current in (0 : ℝ)..time,
            Real.exp ((growth + constant * (feedbackConstant * rho)) * (time - current)) * remaining current := by
  classical
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, thresholdMax, thresholdPositive, thresholdEighth, sourceCap, sourcePositive, sourceFactory⟩ :=
    exists_uniform_actual_coarse_source_response
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨rowCap, rowPositive, rowConstant, rowNonnegative, rowFactory⟩ := exists_uniform_actual_follower_forcing_row
  obtain ⟨partitionCap, partitionPositive, partitionFactory⟩ := exists_uniform_actual_foreign_forcing_partition
  let rawCap := min sourceCap (min rowCap partitionCap)
  have rawPositive : 0 < rawCap := lt_min sourcePositive (lt_min rowPositive partitionPositive)
  have sourceCapBound : rawCap ≤ sourceCap := min_le_left _ _
  have rowCapBound : rawCap ≤ rowCap := (min_le_right _ _).trans (min_le_left _ _)
  have partitionCapBound : rawCap ≤ partitionCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨sourceRadius, sourceRadiusPositive, sourceQuarter, constant, constantOne, rootMin, rootEight, sources⟩ :=
    sourceFactory factorPositive factorSmall
  let radius := min sourceRadius geometryRadius
  let feedbackConstant := rowConstant * geometryConstant
  have geometryNonnegative : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  have feedbackNonnegative : 0 ≤ feedbackConstant := mul_nonneg rowNonnegative geometryNonnegative
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have radiusQuarter : radius ≤ 1 / 4 := (min_le_left _ _).trans sourceQuarter
  refine ⟨radius, lt_min sourceRadiusPositive geometryPositive, radiusQuarter, constant, constantOne,
    geometryConstant, geometryOne, feedbackConstant, feedbackNonnegative, rootMin, rootEight, ?_⟩
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
  intro count phase dipoleAngle shapeRadius monitor prepared path drive finish finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  let followers := Finset.univ.filter (fun receiver : Fin count => receiver.val < drive.val)
  let external := fun receiver : Fin count => Finset.univ.filter
    (fun source : Fin count => drive.val ≤ source.val ∧ source ≠ receiver)
  let remaining := prepared.followerRemainingForcing drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let growth := constant * changed.omega (drive.val + 1) / changed.ratio
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
  have sourceChoice (receiver : Fin count) :
      ∃ chosen : Fin 2 → ℝ → ℝ,
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
              (∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) ≤
            constant * ∫ current in (0 : ℝ)..time,
              Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current) := by
    by_cases below : receiver.val < drive.val
    · have nonterminal : receiver.val + 1 < count := by omega
      obtain ⟨chosen, properties, polar, actual⟩ := sourceEstimate count phase dipoleAngle
        (prepared.enlargeCap sourceCapBound) path receiver nonterminal finish finishNonnegative finishBound
          (fun time inside => (small receiver below time inside).trans (min_le_left _ _))
      dsimp only at actual
      simp only [sizeCapInvariant, rawCapInvariant, forcingCapInvariant, physicalCapInvariant] at actual
      exact ⟨chosen, properties, fun _ => ⟨polar, actual.1, actual.2.1,
        actual.2.2.1.add actual.2.2.2.1, actual.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨fun _ _ => phase (receiver.val + 1), fun _ => ⟨continuous_const, rfl⟩, fun impossible => (below impossible).elim⟩
  choose lift liftProperties liftData using sourceChoice
  let size := fun receiver => prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver
  let raw := fun receiver time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
  let states := fun receiver time => changed.location (receiver.val + 1) ^ 4 * (size receiver time + raw receiver time)
  let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then states receiver time else 0‖
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have sourceGeometry (receiver : Fin count) (below : receiver.val < drive.val) :
      (∀ time : ℝ, 0 ≤ size receiver time) ∧
      ∀ time ∈ Icc 0 finish, prepared.macroSourceState time receiver ≤ geometryConstant * (size receiver time + raw receiver time) := by
    have nonterminal : receiver.val + 1 < count := by omega
    obtain ⟨geometryLift, geometryProperties, geometryPolar, _, _, geometryNonnegative, geometryBounds⟩ :=
      geometryEstimate prepared path receiver nonterminal finish finishNonnegative finishBound
        (fun time inside => (small receiver below time inside).trans (min_le_right _ _))
    have equality := (coherence prepared path receiver finish finishNonnegative finishBound
      (fun time inside => (small receiver below time inside).trans radiusQuarter)
      geometryLift (lift receiver) (fun side => (geometryProperties side).1.continuousOn)
      (fun side => (liftProperties receiver side).1.continuousOn)
      (fun side => (geometryProperties side).2.trans (liftProperties receiver side).2.symm)
      geometryPolar (liftData receiver below).1).2.2 graph coordinate
    refine ⟨?_, ?_⟩
    · intro time
      dsimp only [size]
      have locationPositive := changed.location_pos (receiver.val + 1)
      unfold CascadeSourcePreparedPair.finiteCoordinateSize
      positivity
    · intro time inside
      have actual := (geometryBounds time inside).2
      rw [equality inside] at actual
      exact actual
  have rawNonnegative (receiver : Fin count) (time : ℝ) : 0 ≤ raw receiver time := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have stateNonnegative (receiver : Fin count) (below : receiver.val < drive.val) (time : ℝ) : 0 ≤ states receiver time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4)
      (add_nonneg ((sourceGeometry receiver below).1 time) (rawNonnegative receiver time))
  have envelopeNonnegative (time : ℝ) : 0 ≤ envelope time := norm_nonneg _
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have envelopeContinuous : ContinuousOn envelope (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using
        continuousOn_const.mul ((liftData receiver below).2.1.add (liftData receiver below).2.2.1)
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
  have externalSubset (receiver : Fin count) : external receiver ⊆ Finset.univ.erase receiver := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have selectedData (receiver : Fin count) := selectedContinuous count phase dipoleAngle prepared path receiver
    (external receiver) (externalSubset receiver)
  have remainingContinuous : ContinuousOn remaining (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using
        (continuousOn_const.mul ((selectedData receiver).2.1.mono subset) :
          ContinuousOn (fun current => changed.location (receiver.val + 1) ^ 4 *
            prepared.selectedForeignForcing (external receiver) receiver current) (Icc 0 finish))
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))

  have memberBelow (receiver : Fin count) (member : receiver ∈ followers) : receiver.val < drive.val :=
    (Finset.mem_filter.mp member).2
  have componentBound (receiver : Fin count) (below : receiver.val < drive.val) (time : ℝ) :
      states receiver time ≤ envelope time := by
    have actual := norm_le_pi_norm
      (fun currentReceiver : Fin count => if currentReceiver.val < drive.val then states currentReceiver time else 0) receiver
    simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg (stateNonnegative receiver below time)] using actual
  have macroDominance (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.coarserFollowerEnvelope drive time ≤ geometryConstant * envelope time := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg geometryNonnegative (envelopeNonnegative time))).mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · have actual := mul_le_mul_of_nonneg_left ((sourceGeometry receiver below).2 time inside)
        (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
      have scaled : prepared.weightedMacroSourceState time receiver ≤ geometryConstant * states receiver time := by
        convert actual using 1; dsimp only [CascadeSourcePreparedPair.weightedMacroSourceState, states]; ring
      have bounded := scaled.trans (mul_le_mul_of_nonneg_left (componentBound receiver below time) geometryNonnegative)
      have macroNonnegative : 0 ≤ prepared.weightedMacroSourceState time receiver :=
        mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time receiver)
      simpa only [CascadeSourcePreparedPair.coarserFollowerEnvelope, below, ite_true, Real.norm_eq_abs,
        abs_of_nonneg macroNonnegative]
        using bounded
    · simp only [below, ite_false, norm_zero]
      exact mul_nonneg geometryNonnegative (envelopeNonnegative time)
  have sourceData (receiver : Fin count) (member : receiver ∈ followers) :
      ContinuousOn (fullForcing receiver) (Icc 0 finish) ∧
      ∀ time ∈ Icc 0 finish, size receiver time + raw receiver time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current :=
    ⟨(liftData receiver (memberBelow receiver member)).2.2.2.1,
      (liftData receiver (memberBelow receiver member)).2.2.2.2⟩
  have inputsContinuous (receiver : Fin count) (member : receiver ∈ followers) :
      ContinuousOn (inputs receiver) (Icc 0 finish) := continuousOn_const.mul (sourceData receiver member).1
  have inputsBound (receiver : Fin count) (member : receiver ∈ followers) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      inputs receiver time ≤ feedbackConstant * rho * envelope time + remaining time := by
    have below := memberBelow receiver member
    have different : receiver ≠ drive := by intro same; subst receiver; omega
    obtain ⟨_, _, partitionBound⟩ := partitionEstimate count phase dipoleAngle
      (prepared.enlargeCap partitionCapBound) path (subset inside) receiver drive
    simp only [forcingCapInvariant, physicalCapInvariant, selectedCapInvariant] at partitionBound
    obtain ⟨_, _, _, rowBound⟩ := rowEstimate count phase dipoleAngle (prepared.enlargeCap rowCapBound) path
      time (subset inside) receiver drive below.le
    simp only [selectedCapInvariant, envelopeCapInvariant, different, ite_false, add_zero] at rowBound
    have remainingComponent : changed.location (receiver.val + 1) ^ 4 *
        prepared.selectedForeignForcing (external receiver) receiver time ≤ remaining time := by
      have actual := norm_le_pi_norm (fun currentReceiver : Fin count => if currentReceiver.val < drive.val then
        changed.location (currentReceiver.val + 1) ^ 4 *
          prepared.selectedForeignForcing (external currentReceiver) currentReceiver time else 0) receiver
      have componentNonnegative : 0 ≤ changed.location (receiver.val + 1) ^ 4 *
          prepared.selectedForeignForcing (external receiver) receiver time :=
        mul_nonneg (pow_nonneg (changed.location_pos _).le 4) ((selectedData receiver).1 time)
      simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg componentNonnegative] using actual
    have scaledPartition := mul_le_mul_of_nonneg_left partitionBound (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    apply scaledPartition.trans
    rw [mul_add]
    have rowEnlarged := rowBound.trans (mul_le_mul_of_nonneg_left (macroDominance time inside)
      (mul_nonneg rowNonnegative rhoNonnegative))
    have rowIdentity : rowConstant * rho * (geometryConstant * envelope time) =
        feedbackConstant * rho * envelope time := by dsimp only [feedbackConstant]; ring
    rw [rowIdentity] at rowEnlarged
    exact add_le_add rowEnlarged remainingComponent

  have forcingContinuous : ContinuousOn (fun time => feedbackConstant * rho * envelope time + remaining time) (Icc 0 finish) :=
    (continuousOn_const.mul envelopeContinuous).add remainingContinuous
  have forcingNonnegative (time : ℝ) : 0 ≤ feedbackConstant * rho * envelope time + remaining time :=
    add_nonneg (mul_nonneg (mul_nonneg feedbackNonnegative rhoNonnegative) (envelopeNonnegative time)) (remainingNonnegative time)
  have propagator (receiver : Fin count) (member : receiver ∈ followers) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      states receiver time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * inputs receiver current := by
    have actual := mul_le_mul_of_nonneg_left ((sourceData receiver member).2 time inside)
      (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    have integralIdentity : (∫ current in (0 : ℝ)..time,
        Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * inputs receiver current) =
        changed.location (receiver.val + 1) ^ 4 * ∫ current in (0 : ℝ)..time,
          Real.exp (constant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro current _
      dsimp only [inputs]
      ring
    rw [integralIdentity]
    convert actual using 1; ring

  have ratesBound (receiver : Fin count) (member : receiver ∈ followers) :
      constant * changed.omega (receiver.val + 1) ≤ growth :=
    (changed.coarse_follower_rate_gap constant frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound])
      constantNonnegative receiver.val drive.val (memberBelow receiver member)).2.1
  have masked := General.norm_masked_exponential_volterra_le followers inputsContinuous forcingContinuous constantNonnegative
    (fun receiver member time _ => stateNonnegative receiver (memberBelow receiver member) time)
    (fun time _ => forcingNonnegative time) ratesBound inputsBound propagator
  have preliminary (time : ℝ) (inside : time ∈ Icc 0 finish) :
      envelope time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (feedbackConstant * rho * envelope current + remaining current) := by
    simpa only [followers, Finset.mem_filter, Finset.mem_univ, true_and] using masked time inside
  have initial : envelope 0 = 0 := le_antisymm (by simpa only [intervalIntegral.integral_same, mul_zero] using
    (preliminary 0 ⟨le_rfl, finishNonnegative⟩)) (envelopeNonnegative 0)
  have resolved := exponential_volterra_gronwall (initial := 0) (rate := growth) (feedback := feedbackConstant * rho)
    (multiplier := constant) envelopeContinuous remainingContinuous (mul_nonneg feedbackNonnegative rhoNonnegative)
    constantNonnegative finishNonnegative (by
      intro time inside
      simpa only [zero_mul, zero_add, add_comm] using preliminary time inside)
  refine ⟨lift, liftProperties, fun receiver below => (liftData receiver below).1,
    envelopeContinuous, remainingContinuous, envelopeContinuous.intervalIntegrable_of_Icc finishNonnegative,
    remainingContinuous.intervalIntegrable_of_Icc finishNonnegative, initial, macroDominance, ?_⟩
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have originalKernel : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by fun_prop
  have resolvedKernel : Continuous (fun current : ℝ =>
      Real.exp ((growth + constant * (feedbackConstant * rho)) * (time - current))) := by fun_prop
  exact ⟨(originalKernel.continuousOn.mul (forcingContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1,
    (resolvedKernel.continuousOn.mul (remainingContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1,
    preliminary time inside, by simpa only [zero_mul, zero_add] using resolved time inside⟩

end EulerNonuniqueness.Paper

