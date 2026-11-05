import EulerNonuniqueness.Section5.CascadeCoMovingContourHorizonConfinement
import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeHorizonTolerance

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_cascade_comoving_shape_improvement_on_horizon
    (factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ monitor > 0, ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ horizon → scales.amplitude = scaleRoot ^ 3 →
    1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha → scales.strain ≤ 1 →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    terminal < forwardHorizon →
    (∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ current ∈ Ico 0 terminal, margin < infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ current ∈ Icc 0 terminal, ∀ receiver source,
      cascadeInternalGapMonitor scales factor receiver source (trajectory.movingFamily.cascadeCenters current) ≤ 0) →
    (∀ current ∈ Icc 0 terminal, ∀ label,
      cascadeExtentMonitor scales label (trajectory.movingFamily.cascadeCenters current) ≤ 0) →
    (∀ current ∈ Icc 0 terminal, ∀ receiver source,
      cascadeAnchorLowerMonitor scales receiver source (trajectory.movingFamily.cascadeCenters current) ≤ 0) →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ current ∈ Icc 0 terminal, ∀ index, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < monitor) →
    (∀ current ∈ Icc 0 terminal, ∀ index, (trajectory.curve current).2.2 index ∈ contourContinuousVectorSubmodule) →
    ∀ current ∈ Icc 0 terminal, ∀ index,
      ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < tolerance := by
  obtain ⟨contourMonitor, contourMonitorPositive, contourConstant, contourConstantOne, confinements⟩ :=
    exists_uniform_cascade_comoving_contour_confinement_on_horizon factor factorPositive factorSmall
  obtain ⟨historyRadius, historyPositive, histories⟩ := exists_uniform_spectral_shape_confinement_with_tolerance_on_horizon
  obtain ⟨sourceConstant, sourceConstantOne, sourceBounds⟩ := Scales.exists_uniform_cascade_local_material_scale_bound factor factorPositive factorSmall
  let constant := max contourConstant sourceConstant
  have constantOne : 1 ≤ constant := contourConstantOne.trans (le_max_left _ _)
  refine ⟨min contourMonitor historyRadius, lt_min contourMonitorPositive historyPositive, ?_⟩
  intro horizon tolerance horizonNonnegative tolerancePositive
  obtain ⟨contourRoot, contourRootEight, confined⟩ := confinements horizon horizonNonnegative
  obtain ⟨historyRoot, historyRootEight, improved⟩ := histories constant horizon tolerance (by linarith)
    horizonNonnegative tolerancePositive
  refine ⟨max contourRoot (max historyRoot (192 * sourceConstant)),
    contourRootEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge terminal terminalNonnegative terminalBound amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe internal extent anchorSeparation lengthSmall radiusInternal radiusLocation shapeSmall shapeMember
  have rootContour : contourRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootHistory : historyRoot ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
  have rootEight : 8 ≤ scaleRoot := contourRootEight.trans rootContour
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < scales.frequency := by linarith
  have ratioPositive : 0 < scales.ratio := by linarith
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have projected := confined scales scaleRoot rootContour terminal terminalNonnegative terminalBound amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe internal extent anchorSeparation lengthSmall radiusInternal radiusLocation
    (fun current inside label => (shapeSmall current inside label).trans_le (min_le_left _ _)) shapeMember
  intro time inside label
  obtain ⟨⟨index, patch⟩, labelIdentity⟩ := finProdFinEquiv.surjective label
  subst label
  let frequency := scales.omega (index.val + 1)
  let distance := factor * scales.length (index.val + 1) / 400
  let weight := scales.cascadeLocalExteriorWeight factor (index.val + 1)
  have scalar := sourceBounds scales scaleRoot amplitudeIdentity rootEight frequencyLarge ratioLarge strainSmall (index.val + 1)
  have frequencyBound : 1 ≤ frequency := frequencyLarge.trans
    (scales.omega_ge_frequency frequencyPositive (by linarith) _)
  have distancePositive : 0 < distance := div_pos (mul_pos factorPositive (scales.length_pos _)) (by norm_num)
  have radius : (trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1) :=
    radiusIdentity index patch
  have densityMagnitude : |configuration.density (finProdFinEquiv (index, patch))| = scaleRoot ^ 3 * frequency ^ 4 := by
    rw [densityIdentity, ← Real.norm_eq_abs, norm_mul, norm_mul, norm_patchSign, one_mul,
      Real.norm_of_nonneg amplitudePositive.le, Real.norm_of_nonneg (show 0 ≤ scales.omega (index.val + 1) ^ 4 by positivity),
      amplitudeIdentity]
  have small : 192 * (trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).radius ≤ distance := by
    have rootBound : 192 * sourceConstant ≤ scaleRoot :=
      (le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)
    have denominator : 0 < scaleRoot * frequency := mul_pos rootPositive (by linarith)
    have fraction : sourceConstant / (scaleRoot * frequency) ≤ 1 / 192 := by
      apply (div_le_iff₀ denominator).2
      nlinarith [mul_le_mul_of_nonneg_left frequencyBound rootPositive.le]
    have divided := scalar.2.2.2.1.trans fraction
    rw [radius]
    have multiplied := (div_le_iff₀ distancePositive).mp divided
    linarith
  have evolution := trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity
    initialCircles marginPositive terminalNonnegative beforeFinal safe
  have sources (current : ℝ) (currentInside : current ∈ Icc 0 terminal) :=
    (trajectory.movingFamily.cascade_eventually_comoving_source_envelopes scales evolution currentInside
      densityIdentity radiusIdentity amplitudePositive frequencyLarge ratioLarge alphaPositive
      factor factorPositive factorSmall (internal current currentInside) (extent current currentInside) (anchorSeparation current currentInside)
      lengthSmall radiusInternal radiusLocation index patch).self_of_nhds
  apply improved scaleRoot rootHistory terminal terminalNonnegative terminalBound trajectory initialCircles initialClock marginPositive beforeFinal safe
    (finProdFinEquiv (index, patch)) frequency distance weight frequencyBound densityMagnitude distancePositive scalar.1
    (scalar.2.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))) small
    (fun current currentInside => trajectory.movingFamily.exterior_domain_gap_of_center_gaps
      (finProdFinEquiv (index, patch)) (sources current currentInside).1)
    (fun current currentInside => (sources current currentInside).2.1)
    (fun current currentInside => (shapeSmall current currentInside _).trans_le (min_le_right _ _))
    ?_ time inside
  intro current currentInside
  have bound := projected current currentInside index patch
  have denominator : 0 < scaleRoot ^ 2 * frequency ^ 2 := by positivity
  have enlarged : (contourConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) ≤
      (constant + 1) / (scaleRoot ^ 2 * frequency ^ 2) :=
    div_le_div_of_nonneg_right (add_le_add_right (le_max_left _ _) _) denominator.le
  have positive : 0 ≤ (contourConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) := by positivity
  exact bound.le.trans ((by linarith :
    (contourConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2) / 8 ≤
      (contourConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)).trans enlarged)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory



