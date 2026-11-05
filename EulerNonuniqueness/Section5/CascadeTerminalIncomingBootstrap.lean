import EulerNonuniqueness.Section5.CascadeJointIncomingBootstrap
import EulerNonuniqueness.Section5.CascadeInitialSharpState
import EulerNonuniqueness.Section5.CascadeTerminalSectionData
import EulerNonuniqueness.Section5.CascadeTerminalSourcePhase

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_terminal_incoming_bootstrap (orbit : SeparatingOrbit)
    (_normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime initialError : ℝ)
    (_errorNonnegative : 0 ≤ initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ profileConstant ≥ (1 : ℝ),
      ∃ costMagnitude ≥ (1 : ℝ), ∃ leadingMagnitude ≥ (1 : ℝ), ∃ additiveMagnitude ≥ (0 : ℝ),
      let accuracy := 1 / (64 * (1 + profileConstant))
      let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
        (accuracy / 3) * additiveMagnitude)
      1 ≤ profileMagnitude ∧
      ∃ fullProfileConstant ≥ (1 : ℝ), ∃ sourceMagnitude ≥ (1 : ℝ),
      ∃ targetRadius > (0 : ℝ), targetRadius ≤ 1 / 4 ∧
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointSize > (0 : ℝ),
      endpointSize ≤ 1 ∧ ∀ precision : ℝ, 0 < precision →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ boundaryConstant : ℝ, 1 ≤ boundaryConstant →
      (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count,
      ∀ source : Fin count, index.val + 1 = source.val → source.val + 1 = count →
      PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
      ∀ finish ∈ Icc 0 path.stop,
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      let origin := (0 : ℝ)
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
      (∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
        (|unstableShape motion time receiver| + |stableShape motion time receiver| < radius / 2) ∧
        |radialShape motion time receiver| < 1 / 8) ∧
      ((∀ time ∈ Icc 0 finish, |radialShape motion time index| < 1 / 2) ∧
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| < targetRadius / 2) ∧
      ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let state := fun time => prepared.finiteCoordinateSize graph coordinate lift index time + raw time
      let sharp := fun time => prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) + raw time
      let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
      ContinuousOn shape (Icc 0 finish) ∧ shape 0 = 0 ∧
      (∀ time ∈ Icc 0 finish,
        shape time < profileMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        shape time ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ContinuousOn state (Icc 0 finish) ∧ state 0 = 0 ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * state time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        state time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        sharp time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
        (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
        (∀ receiver : Fin count, receiver.val < index.val → ∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
              Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
        ∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
          prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤ precision := by
  classical
  let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := max 4 (modelBound + 1)
  let magnitude := modelBound + 2
  have boundThree : 3 ≤ modelBound := le_max_left _ _
  have positiveBound : ‖orbit.positive sectionTime‖ ≤ modelBound :=
    (le_max_left _ _).trans (le_max_right _ _)
  have negativeBound : ‖orbit.negative sectionTime‖ ≤ modelBound :=
    (le_max_right _ _).trans (le_max_right _ _)
  have extentFour : 4 ≤ extent := le_max_left _ _
  have boundExtent : modelBound + 1 ≤ extent := le_max_right _ _
  have extentOne : 1 ≤ extent := by linarith
  have magnitudeNonnegative : 0 ≤ magnitude := by dsimp only [magnitude]; linarith
  have distanceNonnegative : 0 ≤ separationRadius orbit sectionTime := by linarith
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, factors⟩ := exists_uniform_actual_joint_incoming_bootstrap
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, rootEight, radius, radiusPositive, radiusQuarter,
    endpointSize, endpointPositive, endpointOne, parameters⟩ := factors factorPositive factorSmall
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, profileMagnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, targetRadius, targetRadiusPositive,
    targetRadiusQuarter, rootMin, rootEight, radius, radiusPositive, radiusQuarter,
    endpointSize, endpointPositive, endpointOne, ?_⟩
  intro precision precisionPositive
  obtain ⟨baseRatio, baseTwo, scalesFactory⟩ := parameters precision precisionPositive extent magnitude
    (separationRadius orbit sectionTime) (1 / 16) extentOne magnitudeNonnegative distanceNonnegative
    (by norm_num) (by norm_num)
  refine ⟨max baseRatio 128, baseTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound boundaryConstant boundaryOne ratioSeparation
  have ratioBase : baseRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := baseTwo.trans ratioBase
  have ratioLarge' : 128 ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have amplitudePositive : 0 < scales.amplitude := by
    rw [amplitudeIdentity]
    have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (rootEight.trans rootLarge)
    positivity
  have thresholdSmall : threshold ≤ 1 / 2 := (thresholdBound.trans thresholdEighth).trans (by norm_num)
  filter_upwards [scalesFactory scales scaleRoot rootLarge amplitudeIdentity ratioBase alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant 0
      boundaryOne le_rfl ratioSeparation,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (max 1 (16 * separationRadius orbit sectionTime))]
    with frequency estimate geometry frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index source adjacent terminal _prescribed finish finishInside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have nonterminal : index.val + 1 < count := by omega
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have finerEq (other : Fin count) (finer : index.val < other.val) : other = source := by
    apply Fin.ext
    omega
  have sourceLarge : separationRadius orbit sectionTime ≤ changed.omega (source.val + 1) / 16 := by
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (source.val + 1)
    have bound := (le_max_right _ _).trans frequencyLarge
    change frequency ≤ changed.omega (source.val + 1) at omegaBound
    linarith
  have initial := cascade_terminal_outgoing_initial_data_of_section orbit sectionTime
    ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) (by linarith only [separationClose, errorSmall]) outgoing
    path.evolution path.stopPositive.le amplitudePositive frequencyPositive ratioPositive prepared.commonInitial source terminal
  dsimp only at initial
  let direction := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
    Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  have directionNorm : ‖direction‖ = 1 := by simp [direction, norm_mul, Complex.norm_exp, Complex.mul_re]
  have firstInitial : ‖firstDipoleSeparation motion 0 source -
      (changed.length (source.val + 1) : ℂ) * direction‖ ≤ changed.length (source.val + 1) / 64 := by
    simpa [firstDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      direction, changed, terminal, motion] using initial.1
  have secondInitial : ‖secondDipoleSeparation motion 0 source -
      (changed.length (source.val + 1) : ℂ) * (-direction)‖ ≤ changed.length (source.val + 1) / 64 := by
    simpa [secondDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      direction, changed, terminal, motion] using initial.2.1
  have projectionInitial : (3 / 4 : ℝ) * changed.length (source.val + 1) * separationRadius orbit sectionTime ≤
      (Complex.I * star direction * (firstDipoleCenter motion 0 source - secondDipoleCenter motion 0 source)).re := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, direction, changed, terminal, motion] using initial.2.2.1
  have upperInitial : ‖firstDipoleCenter motion 0 source - secondDipoleCenter motion 0 source‖ ≤
      (5 / 4 : ℝ) * changed.length (source.val + 1) * separationRadius orbit sectionTime := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, changed, terminal, motion] using initial.2.2.2
  have actualExtents := prepared.toCascadeMaterialPreparedPair.initial_extent_bound
    thresholdSmall boundThree positiveBound negativeBound source
  have actualExtent (patch : Fin 4) : ‖patchCentroid motion 0 source patch - quadrupoleCenter motion 0 source‖ ≤
      modelBound * changed.length (source.val + 1) := by
    have bound := (norm_le_pi_norm (prepared.trajectory.blockExtentVector source 0) patch).trans actualExtents
    rw [prepared.trajectory.blockExtentVector_eq_centroid_offset (fun _ => rfl)
      (by constructor <;> norm_num) source patch] at bound
    exact bound
  have referenceData := prepared.referenceWitness.evolution.reference_initial_center_and_asymmetry
    (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial source
  have referenceExtent (patch : Fin 4) :
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 source‖ ≤
          2 * changed.length (source.val + 1) := by
    rw [referenceData.1, prepared.referenceWitness.evolution.reference_initial_centroid
      (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial source patch]
    exact initialDiskCenter_offset_bound changed _ _ _
      ((prepared.referenceWitness.initial source).1.trans thresholdSmall) patch
  have domains (patch : Fin 4) : motion.domain 0 source patch ⊆
      Metric.closedBall (quadrupoleCenter motion 0 source) (extent * changed.length (source.val + 1)) := by
    intro position member
    have domain := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl)
      (by constructor <;> norm_num) source patch member
    rw [Metric.mem_closedBall, dist_eq_norm] at domain ⊢
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion 0 source patch)
      (quadrupoleCenter motion 0 source)
    have radiusBound := (geometry (source.val + 1)).2.1
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) / 1000 at radiusBound
    change ‖position - patchCentroid motion 0 source patch‖ ≤ 2 * changed.radius (source.val + 1) at domain
    have lengthPositive := changed.length_pos (source.val + 1)
    nlinarith only [triangle, actualExtent patch, domain, radiusBound, lengthPositive,
      mul_le_mul_of_nonneg_right boundExtent lengthPositive.le]
  have sharp := prepared.initial_sharp_state_bound path amplitudePositive frequencyPositive ratioPositive
    thresholdSmall boundThree positiveBound negativeBound source
  have sourceRates : 2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤
      (1 / 16 : ℝ) * changed.omega (source.val + 1) := by
    have recurrence : changed.omega (source.val + 1) = changed.omega (index.val + 1) * changed.ratio := by
      rw [← adjacent]
      simp only [Scales.omega, pow_succ]
      ring
    rw [recurrence]
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have sqrtTwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
    have ratioActual : 128 ≤ changed.ratio := ratioLarge'
    nlinarith only [mul_le_mul_of_nonneg_right ratioActual omegaPositive.le,
      mul_le_mul_of_nonneg_right sqrtTwo omegaPositive.le]
  have nearest : index.val + 2 = count := by omega
  have applyEstimate := estimate count phase dipoleAngle prepared path index nonterminal
    (fun _ => 0) (fun _ => separationRadius orbit sectionTime) (fun _ => direction)
  dsimp only at applyEstimate
  intro exposure
  refine applyEstimate ?_ ?_ (fun _ => magnitude) ?_ ?_ ?_ ?_ (fun _ => 0) ?_ ?_ ?_ ?_ finish finishInside ?_ ?_
  · intro other finer
    rw [finerEq other finer]
    exact ⟨le_rfl, path.stopPositive.le, (by linarith), sourceLarge, directionNorm,
      firstInitial, secondInitial, projectionInitial, upperInitial⟩
  · intro other finer time inside
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    rw [finerEq other finer]
    constructor
    · intro patch
      exact (referenceExtent patch).trans (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ extent)
        (changed.length_pos _).le)
    · intro patch
      exact (actualExtent patch).trans (mul_le_mul_of_nonneg_right (by linarith : modelBound ≤ extent)
        (changed.length_pos _).le)
  · intro other finer
    refine ⟨magnitudeNonnegative, ?_⟩
    intro time inside
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    rw [finerEq other finer]
    simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using sharp
  · intro other finer
    exact le_rfl
  · intro other finer
    exact le_rfl
  · intro other finer time inside patch
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    rw [finerEq other finer]
    exact domains patch
  · intro other
    rfl
  · rw [nearest, changed.predictedTime_terminal]
    norm_num
  · intro other finer
    rw [finerEq other finer, terminal, changed.predictedTime_terminal]
    norm_num
  · intro other finer
    exact le_rfl
  · intro other finer
    rw [finerEq other finer]
    exact sourceRates
  · simpa only [sub_zero] using exposure

end EulerNonuniqueness.Paper
