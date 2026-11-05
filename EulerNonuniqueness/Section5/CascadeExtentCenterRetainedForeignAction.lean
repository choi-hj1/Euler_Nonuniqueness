import EulerNonuniqueness.Section5.CascadeExtentCenterLocalForeignRate
import EulerNonuniqueness.Section5.CascadeExtentMacroSourceStateBound
import EulerNonuniqueness.Section5.CascadeForeignPatchAbsoluteCoefficientBound
import EulerNonuniqueness.Section5.CascadeRetainedCenterMomentHistory
import EulerNonuniqueness.Section5.CascadeExternalVelocityContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_extent_center_retained_foreign_action :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∀ extent ≥ (1 : ℝ), ∀ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let location := changed.location (index.val + 1)
    let center := fun time => quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index
    let velocity := fun time => prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
      prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time
    let moment := relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index
    let foreign := fun time => (∑ patch : Fin 4,
      ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
        biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖) /
          (4 * location)
    ContinuousOn foreign (Icc 0 path.stop) ∧
    ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
    (∀ time ∈ Icc start finish, ∀ patch,
      ‖patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index‖ ≤
        extent * changed.length (index.val + 1)) →
    (∀ time ∈ Icc start finish, ∀ patch,
      ‖patchCentroid second.patchMotion time index patch - quadrupoleCenter second.patchMotion time index‖ ≤
        extent * changed.length (index.val + 1)) →
    IntervalIntegrable (fun time => ‖moment time‖) volume start finish ∧
    IntervalIntegrable foreign volume start finish ∧
    (∀ time ∈ Icc start finish,
      ‖velocity time‖ / location ≤ tolerance * ‖moment time‖ + foreign time + tolerance) ∧
    ‖center finish‖ / location ≤ ‖center start‖ / location +
      tolerance * (∫ time in start..finish, ‖moment time‖) +
      (∫ time in start..finish, foreign time) + tolerance * (finish - start) := by
  obtain ⟨rateCap, rateCapPositive, rateFactory⟩ := exists_uniform_actual_extent_center_local_foreign_rate
  obtain ⟨stateCap, stateCapPositive, rawConstant, rawNonnegative, rawIdentity, states⟩ :=
    exists_uniform_actual_extent_macro_source_state_bound
  let rawCap := min rateCap stateCap
  have capPositive : 0 < rawCap := lt_min rateCapPositive stateCapPositive
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall extent extentOne tolerance tolerancePositive
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨constant, constantNonnegative, rates⟩ := rateFactory factorPositive factorSmall
  obtain ⟨patchConstant, patchNonnegative, patchFactory⟩ :=
    exists_uniform_actual_foreign_patch_absolute_coefficient_bound factor factorPositive factorOne
  let reduced := tolerance / (4 * extent)
  let size := 2 * extent + rawConstant + patchConstant + 1
  let transport := tolerance / (2 * (constant + 1) * size)
  have extentPositive : 0 < extent := zero_lt_one.trans_le extentOne
  have sizePositive : 0 < size := by dsimp only [size]; positivity
  have reducedPositive : 0 < reduced := by dsimp only [reduced]; positivity
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have reducedBound : reduced ≤ tolerance := by
    dsimp only [reduced]
    apply (div_le_iff₀ (by positivity : 0 < 4 * extent)).mpr
    nlinarith only [tolerancePositive.le, mul_nonneg tolerancePositive.le (sub_nonneg.mpr extentOne)]
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    rootOne boundaryOne thresholdSmall referenceNonnegative
  filter_upwards [rates extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative reducedPositive,
    patchFactory scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_patch_external_velocity_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_omega_length_lt_location ratioBound alphaPositive transportPositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (1 : ℝ)]
    with frequency rateEstimate patchEstimate velocityContinuity transportEstimate lengthEstimate radiusEstimate strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let location := changed.location (index.val + 1)
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let patchRadius := factor / 39321600 * length
  let moment := relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index
  let foreign := fun time => (∑ patch : Fin 4,
    ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
      biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖) /
        (4 * location)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive ratioOne _)
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive : 0 < location := changed.location_pos _
  have lengthBound : length ≤ location := by simpa only [one_mul] using (lengthEstimate (index.val + 1)).le
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonOne : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos lengthPositive)).mpr
    have radiusBound : changed.radius (index.val + 1) ≤ length := by
      simpa only [one_mul] using (radiusEstimate (index.val + 1)).le
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le radiusBound 2
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have transportBound : omega * (length / location) ≤ transport := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ locationPositive).mpr (transportEstimate (index.val + 1)).le
  have normalizedLengthBound : length / location ≤ omega * (length / location) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right omegaOne (div_nonneg lengthPositive.le locationPositive.le)
  have foreignContinuous : ContinuousOn foreign (Icc 0 path.stop) := by
    exact (continuousOn_finset_sum _ fun patch _ =>
      (velocityContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).norm).div_const _
  have stateCenterInvariant : (prepared.enlargeCap (min_le_right rateCap stateCap)).rawSourceCenteredState =
      prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have stateRawInvariant : (prepared.enlargeCap (min_le_right rateCap stateCap)).rawSourceShapeBudget =
      prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have rateCenterInvariant : (prepared.enlargeCap (min_le_left rateCap stateCap)).rawSourceCenteredState =
      prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rateRawInvariant : (prepared.enlargeCap (min_le_left rateCap stateCap)).rawSourceShapeBudget =
      prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  refine ⟨foreignContinuous, ?_⟩
  intro start startInside finish finishInside firstExtent secondExtent
  have subset : Icc start finish ⊆ Icc 0 path.stop := Icc_subset_Icc startInside.1 finishInside.2
  have momentContinuous : ContinuousOn moment (Icc start finish) := by
    intro time inside
    have actual := path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
    rw [prepared.referenceIdentity] at actual
    exact actual.continuousAt.continuousWithinAt
  have momentIntegrable := momentContinuous.norm.intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have foreignIntegrable := (foreignContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have pointwise (time : ℝ) (inside : time ∈ Icc start finish) :
      ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
        prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location ≤
        tolerance * ‖moment time‖ + foreign time + tolerance := by
    have raw := states extent extentPositive.le (prepared.enlargeCap (min_le_right rateCap stateCap)) path time (subset inside) index
    rw [stateCenterInvariant, stateRawInvariant] at raw
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at raw
    have centeredBound := (raw.2 (secondExtent time inside) (firstExtent time inside)).1
    have rawBound := raw.1
    have radiusNonnegative : 0 ≤ patchRadius := by dsimp only [patchRadius]; positivity
    have radiusSmall : patchRadius ≤ factor / 39321600 * scales.location (index.val + 1) :=
      mul_le_mul_of_nonneg_left lengthBound (by positivity)
    have patchBounds := patchEstimate count orbit sectionTime phase dipoleAngle prepared path index time (subset inside)
      patchRadius radiusNonnegative radiusSmall
    have actual := rateEstimate count phase dipoleAngle (prepared.enlargeCap (min_le_left rateCap stateCap)) path index time
      (subset inside) (firstExtent time inside) (by
        rw [(prepared.enlargeCap (min_le_left rateCap stateCap)).referenceIdentity]
        exact secondExtent time inside)
    dsimp only at actual
    rw [rateCenterInvariant, rateRawInvariant] at actual
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time index := by
      dsimp only [CascadeSourcePreparedPair.rawSourceCenteredState]
      positivity
    have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch :=
      Finset.sum_nonneg fun patch _ => by
        dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
        positivity
    have firstError : constant * omega * (length / location) * epsilon *
        (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤
          constant * (omega * (length / location)) * (2 * extent + rawConstant) := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add centeredBound rawBound)
        (mul_nonneg constantNonnegative (mul_nonneg omegaNonnegative (div_nonneg lengthPositive.le locationPositive.le))),
        mul_nonneg (sub_nonneg.mpr epsilonOne)
          (mul_nonneg (mul_nonneg constantNonnegative (mul_nonneg omegaNonnegative (div_nonneg lengthPositive.le locationPositive.le)))
            (add_nonneg centeredNonnegative rawNonnegative))]
    have secondError : constant * (length / location) * epsilon *
        (∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
          ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
            second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖) ≤
          constant * (omega * (length / location)) * patchConstant := by
      have foreignBound := patchBounds.2.trans (mul_le_of_le_one_right patchNonnegative strainSmall.le)
      have coefficientBound : constant * (length / location) * epsilon ≤ constant * (omega * (length / location)) :=
        (mul_le_mul_of_nonneg_left epsilonOne (mul_nonneg constantNonnegative
          (div_nonneg lengthPositive.le locationPositive.le))).trans (by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left normalizedLengthBound constantNonnegative)
      exact mul_le_mul coefficientBound foreignBound (by positivity) (by positivity)
    have smallError : constant * (omega * (length / location)) * (2 * extent + rawConstant) +
        constant * (omega * (length / location)) * patchConstant ≤ tolerance / 2 := by
      have comparison := mul_le_mul_of_nonneg_right transportBound
        (show 0 ≤ constant * (2 * extent + rawConstant + patchConstant) by positivity)
      have final : constant * transport * (2 * extent + rawConstant + patchConstant) ≤ tolerance / 2 := by
        have identity : (constant + 1) * transport * size = tolerance / 2 := by
          dsimp only [transport]
          field_simp [show constant + 1 ≠ 0 by positivity, sizePositive.ne']
          ring
        have slack : 0 ≤ transport * (constant + 2 * extent + rawConstant + patchConstant + 1) := by positivity
        dsimp only [size] at identity
        nlinarith only [identity, slack]
      nlinarith only [comparison, final]
    have firstPart : reduced * (‖moment time‖ + prepared.rawSourceCenteredState time index) ≤
        tolerance * ‖moment time‖ + tolerance / 2 := by
      have centered := mul_le_mul_of_nonneg_left centeredBound reducedPositive.le
      have identity : reduced * (2 * extent) = tolerance / 2 := by
        dsimp only [reduced]
        field_simp [extentPositive.ne']
        ring
      nlinarith only [centered, identity, mul_le_mul_of_nonneg_right reducedBound (norm_nonneg (moment time))]
    change _ ≤ _ at actual
    exact actual.trans (by nlinarith only [firstPart, firstError, secondError, smallError])
  refine ⟨momentIntegrable, foreignIntegrable, pointwise, ?_⟩
  have retained := path.relative_center_retained_history index startInside.1 finishInside.1 finishInside.2
  simp only [prepared.referenceIdentity] at retained
  have constantIntegrable : IntervalIntegrable (fun _ : ℝ => tolerance) volume start finish := intervalIntegrable_const
  have integrable := ((momentIntegrable.const_mul tolerance).add foreignIntegrable).add constantIntegrable
  have comparison := intervalIntegral.integral_mono_on finishInside.1 retained.2.1 integrable pointwise
  rw [intervalIntegral.integral_add ((momentIntegrable.const_mul tolerance).add foreignIntegrable) constantIntegrable,
    intervalIntegral.integral_add (momentIntegrable.const_mul tolerance) foreignIntegrable,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at comparison
  exact retained.2.2.2.trans (by linarith only [comparison])

end EulerNonuniqueness.Paper
