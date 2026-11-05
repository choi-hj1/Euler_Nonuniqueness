import EulerNonuniqueness.Section5.CascadeCoMovingCappedAnalyticBootstrap
import EulerNonuniqueness.Section5.CascadeGapCappedInitialMonitors
import EulerNonuniqueness.Section5.CascadeSourcePreparedPair
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section4.ReferenceCappedMaterialSolutions

noncomputable section

open Set Metric Filter

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

theorem exists_uniform_gap_capped_source_prepared_cascade_pairs
    (factorCap : ℝ) (capPositive : 0 < factorCap)
    (requestedCap : ℝ) (requestedPositive : 0 < requestedCap)
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (alphaSmall : alpha < 1) (ratioLarge : 2 < ratio)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime : ℝ) :
    ∃ threshold > (0 : ℝ), threshold < 1 / 8 ∧
    ∃ shapeRadius > (0 : ℝ), ∃ factor > (0 : ℝ), factor ≤ 1 / 8 ∧ factor ≤ factorCap ∧
    ∃ monitor > (0 : ℝ), ∃ boundaryConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot → ∃ referenceConstant > (0 : ℝ), referenceConstant ≤ scaleRoot ^ 3 ∧
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, 2 ≤ count → ∀ phase dipoleAngle : ℕ → ℝ,
    Nonempty (CascadeSourcePreparedPair requestedCap ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count) := by
  obtain ⟨thresholdMax, thresholdMaxPositive, referenceFactories⟩ := exists_uniform_reference_capped_material_solutions requestedCap requestedPositive alphaPositive ratioLarge.le
  let threshold := min (thresholdMax / 2) (1 / 16)
  have thresholdPositive : 0 < threshold := lt_min (half_pos thresholdMaxPositive) (by norm_num)
  have thresholdBound : threshold ≤ thresholdMax := (min_le_left _ _).trans (by linarith)
  have thresholdSmall : threshold < 1 / 8 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨referenceAmplitude, referenceAmplitudePositive, references⟩ :=
    referenceFactories threshold thresholdPositive thresholdBound
  obtain ⟨shapeRadius, shapePositive, _, initialFamilies⟩ := exists_uniform_gap_capped_cascade_initial_family_with_monitors factorCap capPositive
  obtain ⟨factor, factorPositive, factorSmall, factorCapped, bound, boundThree, families⟩ := initialFamilies orbit normalized sectionTime
  obtain ⟨monitor, monitorPositive, monitorCap, boundaryConstant, boundaryOne, analyticFactories⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_capped_cascade_comoving_analytic_bootstrap requestedCap requestedPositive factor factorPositive (by linarith)
  obtain ⟨analyticRoot, analyticRootEight, analytic⟩ := analyticFactories shapeRadius 1 shapePositive (by norm_num)
  let rootMin := max 8 (max referenceAmplitude analyticRoot)
  refine ⟨threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive, factor, factorPositive,
    factorSmall, factorCapped, monitor, monitorPositive, boundaryConstant, boundaryOne, rootMin, le_max_left _ _, ?_⟩
  intro scaleRoot rootLarge
  have rootEight : 8 ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootPositive : 0 < scaleRoot := by linarith
  have rootReference : referenceAmplitude ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
  have rootAnalytic : analyticRoot ≤ scaleRoot := (le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)
  have amplitudeLarge : referenceAmplitude ≤ scaleRoot ^ 3 := by
    have squareOne : (1 : ℝ) ≤ scaleRoot ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left squareOne rootPositive.le]
  have amplitudePositive : 0 < scaleRoot ^ 3 := by positivity
  obtain ⟨referenceConstant, referenceConstantPositive, referenceAmplitudeBound, referenceSolutions⟩ :=
    references (scaleRoot ^ 3) amplitudeLarge
  refine ⟨referenceConstant, referenceConstantPositive, referenceAmplitudeBound, ?_⟩
  let base : Scales := ⟨alpha, scaleRoot ^ 3, ratio, 0⟩
  filter_upwards [referenceSolutions, eventually_ge_atTop (1 : ℝ),
    base.eventually_cascade_geometric_scale_smallness amplitudePositive ratioLarge.le alphaPositive
      factorPositive (by linarith) boundThree,
    (base.strain_tendsto_zero ratioLarge.le alphaPositive).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency referenceAvailable frequencyOne geometry strainSmall
  intro count countLarge phase dipoleAngle
  let scales : Scales := ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩
  obtain ⟨referenceWitness, referenceShapeCap, referenceSolution⟩ := referenceAvailable count (by omega)
    (fun index => phase (index.val + 1))
  let reference := referenceWitness.trajectory.movingFamily.patchMotion
  let unstable := referenceWitness.unstable
  have initial := referenceWitness.initial
  have initialHalf : ReferenceInitialDisks scales reference (fun index => phase (index.val + 1)) unstable (1 / 2) := by
    intro index
    exact ⟨(initial index).1.trans (by linarith), (initial index).2⟩
  obtain ⟨configuration, densities, radii, gap, gapPositive, margin, marginPositive, marginShape,
    marginUnit, marginSlack, trajectory, commonInitial, initialMargin, initialInternal, initialLocation, preserves⟩ :=
    families scales amplitudePositive (zero_lt_one.trans_le frequencyOne) (by linarith) count (by omega)
      (fun index => phase (index.val + 1)) unstable dipoleAngle reference initialHalf
      (fun index => (geometry (index.val + 1)).1) (fun index => (geometry (index.val + 1)).2.1)
  refine ⟨{
    referenceShapeCap := referenceShapeCap
    monitorCap := monitorCap
    referenceWitness := referenceWitness
    referenceIdentity := rfl
    unstableIdentity := rfl
    reference := reference
    unstable := unstable
    referenceSolution := referenceSolution
    referenceInitial := initial
    configuration := configuration
    densityIdentity := densities
    radiusIdentity := radii
    gap := gap
    gapPositive := gapPositive
    margin := margin
    marginPositive := marginPositive
    marginShape := marginShape
    marginUnit := marginUnit
    marginSlack := marginSlack
    trajectory := trajectory
    commonInitial := commonInitial
    initialMargin := initialMargin
    initialInternal := initialInternal
    initialLocation := initialLocation
    continuousVectors := preserves
    analyticControl := ?_
  }⟩
  intro terminal terminalNonnegative terminalBound internal extent separation anchorNorm
  exact analytic scales scaleRoot rootAnalytic rfl frequencyOne ratioLarge.le alphaPositive strainSmall.le
    (by omega) trajectory densities radii (fun _ => rfl) rfl marginPositive marginShape marginUnit marginSlack initialMargin
    (fun index => (geometry (index.val + 1)).2.2.1) (fun index => (geometry (index.val + 1)).2.1)
    (fun index => (geometry (index.val + 1)).2.2.2) terminal terminalNonnegative terminalBound (by linarith)
    internal extent separation anchorNorm (fun time inside label => preserves time ⟨inside.1, by linarith [inside.2]⟩ label)

end EulerNonuniqueness.Paper




