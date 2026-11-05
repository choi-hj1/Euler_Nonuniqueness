import EulerNonuniqueness.Section5.CascadeExtentFirstMomentCompactWindow
import EulerNonuniqueness.Section5.CascadeExtentMacroSourceStateBound
import EulerNonuniqueness.Section5.CascadeFaithfulMemoryCompactWindow
import EulerNonuniqueness.Section5.CascadeExtentCenterRetainedForeignAction

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem compact_foreign_action_unweight
    {forcing : ℝ → ℝ} {start finish omega span : ℝ}
    (regular : ContinuousOn forcing (Icc start finish)) (nonnegative : ∀ time, 0 ≤ forcing time)
    (ordered : start ≤ finish) (omegaNonnegative : 0 ≤ omega)
    (normalizedSpan : omega * (finish - start) ≤ span) :
    IntervalIntegrable (fun time => Real.exp (-omega * (time - start)) * forcing time) volume start finish ∧
      (∫ time in start..finish, forcing time) ≤ Real.exp span *
        ∫ time in start..finish, Real.exp (-omega * (time - start)) * forcing time := by
  have weightedContinuous : ContinuousOn (fun time => Real.exp (-omega * (time - start)) * forcing time)
      (Icc start finish) :=
    (by fun_prop : Continuous (fun time : ℝ => Real.exp (-omega * (time - start)))).continuousOn.mul regular
  have weightedI := weightedContinuous.intervalIntegrable_of_Icc (μ := volume) ordered
  refine ⟨weightedI, ?_⟩
  have comparison := intervalIntegral.integral_mono_on ordered (regular.intervalIntegrable_of_Icc ordered)
    (weightedI.const_mul (Real.exp span)) (by
      intro time inside
      have exponent : 0 ≤ span - omega * (time - start) := by
        have scaled := mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 start) omegaNonnegative
        linarith only [scaled, normalizedSpan]
      have lower : 1 ≤ Real.exp span * Real.exp (-omega * (time - start)) := by
        rw [← Real.exp_add]
        have identity : span + -omega * (time - start) = span - omega * (time - start) := by ring
        rw [identity]
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr exponent
      convert mul_le_mul_of_nonneg_right lower (nonnegative time) using 1 <;> ring)
  rw [intervalIntegral.integral_const_mul] at comparison
  exact comparison

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_compact_sharp_state_retained_budget :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∀ extent ≥ (1 : ℝ), ∀ span ≥ (0 : ℝ), ∀ memoryConstant ≥ (0 : ℝ),
    ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let omega := changed.omega (index.val + 1)
    let location := changed.location (index.val + 1)
    let moment := relativeNormalizedFirstMoment changed first second index
    let center := fun time => quadrupoleCenter first time index - quadrupoleCenter second time index
    let foreign := fun time => (∑ patch : Fin 4,
      ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
        biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * location)
    let rate := memoryConstant * (1 + omega * (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2))
    let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
      (omega * prepared.rawSourceCenteredState current index + prepared.physicalForeignSourceForcing index current)
    ContinuousOn memory (Icc 0 path.stop) ∧ memory 0 = 0 ∧
    ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
      IntervalIntegrable (fun time => Real.exp (-omega * (time - start)) * foreign time) volume start finish ∧
      (omega * (finish - start) ≤ span →
        (∀ time ∈ Icc start finish, ∀ patch,
          ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ extent * changed.length (index.val + 1)) →
        (∀ time ∈ Icc start finish, ∀ patch,
          ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ extent * changed.length (index.val + 1)) →
        prepared.rawSourceCenteredState finish index + ‖moment finish‖ + ‖center finish‖ / location +
            (∑ patch : Fin 4, prepared.rawSourceShapeBudget finish index patch) + memory finish ≤
          constant * (1 + ‖moment start‖ + ‖center start‖ / location + memory start +
            ∫ time in start..finish, Real.exp (-omega * (time - start)) * foreign time)) := by
  obtain ⟨momentCap, momentPositive, moments⟩ := exists_uniform_actual_extent_firstMoment_compact_window
  obtain ⟨shapeCap, shapePositive, rawConstant, rawNonnegative, _, shapes⟩ :=
    exists_uniform_actual_extent_macro_source_state_bound
  obtain ⟨centerCap, centerPositive, centers⟩ := exists_uniform_actual_extent_center_retained_foreign_action
  let rawCap := min momentCap (min shapeCap centerCap)
  have momentCapBound : rawCap ≤ momentCap := min_le_left _ _
  have shapeCapBound : rawCap ≤ shapeCap := (min_le_right _ _).trans (min_le_left _ _)
  have centerCapBound : rawCap ≤ centerCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rawCap, lt_min momentPositive (lt_min shapePositive centerPositive), ?_⟩
  intro factor factorPositive factorSmall extent extentOne span spanNonnegative memoryConstant memoryNonnegative
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨momentConstant, momentNonnegative, momentFactory⟩ := moments factorPositive factorEighth
  obtain ⟨foreignConstant, foreignConstantNonnegative, memoryFactory⟩ :=
    exists_uniform_actual_faithful_memory_compact_window factor factorPositive factorOne
  let baseline := 2 * extent + rawConstant + span +
    Real.exp 1 * (1 + span) * momentConstant * extent ^ 3 * span +
      Real.exp 1 * memoryConstant * (2 * extent * span + foreignConstant * span)
  let momentCoefficient := Real.exp 1 * (1 + span)
  let constant := baseline + momentCoefficient + 1 + Real.exp 1 + Real.exp span
  have baselineNonnegative : 0 ≤ baseline := by dsimp only [baseline]; positivity
  have momentCoefficientNonnegative : 0 ≤ momentCoefficient := by dsimp only [momentCoefficient]; positivity
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [momentFactory extent extentOne span spanNonnegative scales amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    centers factorPositive factorSmall extent extentOne 1 (by norm_num : (0 : ℝ) < 1)
      scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative,
    memoryFactory memoryConstant memoryNonnegative extent extentOne span spanNonnegative scales amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (1 : ℝ)] with frequency momentEstimate centerEstimate memoryEstimate strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let location := changed.location (index.val + 1)
  let moment := relativeNormalizedFirstMoment changed first second index
  let center := fun time => quadrupoleCenter first time index - quadrupoleCenter second time index
  let foreign := fun time => (∑ patch : Fin 4,
    ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
      biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * location)
  let rate := memoryConstant * (1 + omega * (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2))
  let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
    (omega * prepared.rawSourceCenteredState current index + prepared.physicalForeignSourceForcing index current)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive ratioOne _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have locationPositive : 0 < location := changed.location_pos _
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg
    (changed.circulation_pos frequencyPositive (zero_lt_one.trans_le ratioOne) _).le (sq_nonneg _)
  have momentData := momentEstimate count phase dipoleAngle (prepared.enlargeCap momentCapBound) path index
  have centerData := centerEstimate count phase dipoleAngle (prepared.enlargeCap centerCapBound) path index
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at momentData centerData
  rw [prepared.referenceIdentity] at momentData
  have memoryData := memoryEstimate count phase dipoleAngle prepared path index
  obtain ⟨_, _, _, _, _, _, memoryContinuous, _, _, memoryZero, memoryPointwise, memoryWindows⟩ := memoryData
  have foreignContinuous : ContinuousOn foreign (Icc 0 path.stop) := centerData.1
  have foreignNonnegative (time : ℝ) : 0 ≤ foreign time := div_nonneg
    (Finset.sum_nonneg fun patch _ => norm_nonneg _) (mul_pos (by norm_num) locationPositive).le
  have shapeCenterInvariant : (prepared.enlargeCap shapeCapBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have shapeRawInvariant : (prepared.enlargeCap shapeCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  refine ⟨memoryContinuous, memoryZero, ?_⟩
  intro start startInside finish finishInside
  have subset : Icc start finish ⊆ Icc 0 path.stop := Icc_subset_Icc startInside.1 finishInside.2
  have weightedI : IntervalIntegrable (fun time => Real.exp (-omega * (time - start)) * foreign time)
      volume start finish :=
    ((by fun_prop : Continuous (fun time : ℝ => Real.exp (-omega * (time - start)))).continuousOn.mul
      (foreignContinuous.mono subset)).intervalIntegrable_of_Icc finishInside.1
  refine ⟨weightedI, ?_⟩
  intro spanBound firstExtent secondExtent
  have durationBound : finish - start ≤ span :=
    ((le_div_iff₀ omegaPositive).mpr (by simpa only [mul_comm] using spanBound)).trans
      (div_le_self spanNonnegative omegaOne)
  let momentUpper := Real.exp 1 * (‖moment start‖ + momentConstant * extent ^ 3 * span)
  have momentUpperNonnegative : 0 ≤ momentUpper := by dsimp only [momentUpper]; positivity
  have momentBound (time : ℝ) (inside : time ∈ Icc start finish) : ‖moment time‖ ≤ momentUpper := by
    have timeInside : time ∈ Icc start path.stop := ⟨inside.1, inside.2.trans finishInside.2⟩
    have prefixSpan : omega * (time - start) ≤ span :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 start) omegaPositive.le).trans spanBound
    have actual := ((momentData.2.2.2.2 start startInside time timeInside).2.2.2.2 prefixSpan
      (fun current member => firstExtent current ⟨member.1, member.2.trans inside.2⟩)
      (fun current member => secondExtent current ⟨member.1, member.2.trans inside.2⟩)).2
    have sourceNonnegative : 0 ≤ momentConstant * extent ^ 3 * changed.strain * span := by positivity
    have small : momentConstant * extent ^ 3 * changed.strain * span / omega ≤ momentConstant * extent ^ 3 * span :=
      (div_le_self sourceNonnegative omegaOne).trans (by
        convert mul_le_mul_of_nonneg_left strainSmall.le
          (show 0 ≤ momentConstant * extent ^ 3 * span by positivity) using 1 <;> ring)
    exact actual.trans (mul_le_mul_of_nonneg_left (add_le_add_left small _) (Real.exp_pos _).le)
  have centerWindow := centerData.2 start startInside finish finishInside firstExtent secondExtent
  have integratedMoment := intervalIntegral.integral_mono_on finishInside.1 centerWindow.1
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => momentUpper) volume start finish) momentBound
  rw [intervalIntegral.integral_const, smul_eq_mul] at integratedMoment
  have momentAction : (∫ time in start..finish, ‖moment time‖) ≤ span * momentUpper :=
    integratedMoment.trans (mul_le_mul_of_nonneg_right durationBound momentUpperNonnegative)
  have unweightedForeign := (compact_foreign_action_unweight (foreignContinuous.mono subset) foreignNonnegative
    finishInside.1 omegaPositive.le spanBound).2
  let action := ∫ time in start..finish, Real.exp (-omega * (time - start)) * foreign time
  have actionNonnegative : 0 ≤ action := intervalIntegral.integral_nonneg_of_forall finishInside.1
    (fun time => mul_nonneg (Real.exp_pos _).le (foreignNonnegative time))
  have centerBound : ‖center finish‖ / location ≤ ‖center start‖ / location + span * momentUpper + Real.exp span * action + span := by
    have actual := centerWindow.2.2.2
    simp only [one_mul] at actual
    exact actual.trans (add_le_add (add_le_add (add_le_add_left momentAction _) unweightedForeign) durationBound)
  have actualRaw := shapes extent (zero_le_one.trans extentOne) (prepared.enlargeCap shapeCapBound) path finish
    ⟨startInside.1.trans finishInside.1, finishInside.2⟩ index
  rw [shapeCenterInvariant, shapeRawInvariant] at actualRaw
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at actualRaw
  have rawBound := actualRaw.1
  have centeredBound := (actualRaw.2 (secondExtent finish ⟨finishInside.1, le_rfl⟩)
    (firstExtent finish ⟨finishInside.1, le_rfl⟩)).1
  have memoryWindow := (memoryWindows start startInside finish finishInside).2.2.2 spanBound firstExtent (by
    intro time inside patch
    rw [prepared.referenceIdentity]
    exact secondExtent time inside patch)
  have foreignInputSmall : foreignConstant * changed.strain * span / omega ≤ foreignConstant * span :=
    (div_le_self (by positivity : 0 ≤ foreignConstant * changed.strain * span) omegaOne).trans (by
      convert mul_le_mul_of_nonneg_left strainSmall.le (mul_nonneg foreignConstantNonnegative spanNonnegative) using 1 <;> ring)
  have memoryBound : memory finish ≤ Real.exp 1 * (memory start + memoryConstant * (2 * extent * span + foreignConstant * span)) :=
    memoryWindow.2.trans (mul_le_mul_of_nonneg_left (add_le_add_left
      (mul_le_mul_of_nonneg_left (add_le_add_left foreignInputSmall _) memoryNonnegative) _) (Real.exp_pos _).le)
  have combined := add_le_add (add_le_add (add_le_add (add_le_add centeredBound
    (momentBound finish ⟨finishInside.1, le_rfl⟩)) centerBound) rawBound) memoryBound
  have baselineBelow : baseline ≤ constant := by
    dsimp only [constant]; linarith only [momentCoefficientNonnegative, Real.exp_pos (1 : ℝ), Real.exp_pos span]
  have momentCoefficientBelow : momentCoefficient ≤ constant := by
    dsimp only [constant]; linarith only [baselineNonnegative, Real.exp_pos (1 : ℝ), Real.exp_pos span]
  have oneBelow : 1 ≤ constant := by
    dsimp only [constant]; linarith only [baselineNonnegative, momentCoefficientNonnegative, Real.exp_pos (1 : ℝ), Real.exp_pos span]
  have memoryCoefficientBelow : Real.exp 1 ≤ constant := by
    dsimp only [constant]; linarith only [baselineNonnegative, momentCoefficientNonnegative, Real.exp_pos span]
  have actionCoefficientBelow : Real.exp span ≤ constant := by
    dsimp only [constant]; linarith only [baselineNonnegative, momentCoefficientNonnegative, Real.exp_pos (1 : ℝ)]
  have final := add_le_add (add_le_add (add_le_add (add_le_add baselineBelow
    (mul_le_mul_of_nonneg_right momentCoefficientBelow (norm_nonneg (moment start))))
    (mul_le_mul_of_nonneg_right oneBelow (div_nonneg (norm_nonneg (center start)) locationPositive.le)))
    (mul_le_mul_of_nonneg_right memoryCoefficientBelow (memoryPointwise start startInside).1))
    (mul_le_mul_of_nonneg_right actionCoefficientBelow actionNonnegative)
  apply combined.trans
  convert final using 1 <;> dsimp only [baseline, momentCoefficient, momentUpper, action] <;> ring

end EulerNonuniqueness.Paper
