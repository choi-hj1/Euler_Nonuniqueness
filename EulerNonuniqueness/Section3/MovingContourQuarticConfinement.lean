import EulerNonuniqueness.Section3.MovingContourConfinementTube
import EulerNonuniqueness.Section3.MovingContourInteractionInitial
import EulerNonuniqueness.Section3.MovingContourNamedPrefixSlope
import EulerNonuniqueness.Section3.CanonicalInteractionTransverseRecovery
import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseBounds
import EulerNonuniqueness.General.QuarticObservableBootstrap
import EulerNonuniqueness.General.QuarticConfinementBudget

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_quartic_contour_confinement :
    ∃ radius > 0, ∀ forcingConstant terminal : ℝ, 0 ≤ forcingConstant → 0 ≤ terminal →
    ∃ rootMin ≥ (8 : ℝ), ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ (frequency distance weight mass : Fin count → ℝ),
    (∀ index, 1 ≤ frequency index) →
    (∀ index, |configuration.density index| = scaleRoot ^ 3 * frequency index ^ 4) →
    (∀ index, weight index ≤ forcingConstant * frequency index) →
    (∀ index, (trajectory.movingFamily.patch index).radius / distance index ≤
      forcingConstant / (scaleRoot * frequency index)) →
    (∀ index, weight index ^ 2 + mass index * weight index / distance index ^ 2 ≤
      forcingConstant * frequency index ^ 2) →
    ContourConfinementTube trajectory terminal radius distance weight mass →
    ∀ current ∈ Icc 0 terminal, ∀ index,
      ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index current)‖ <
        ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency index ^ 2)) / 8 := by
  obtain ⟨slopeRadius, slopePositive, slopeConstant, slopeOne, slopes⟩ :=
    exists_uniform_named_contour_prefix_slope_radius
  obtain ⟨recoveryRadius, recoveryPositive, recoveryCoefficient, recoveryNonnegative, recoveryLoss,
    lossNonnegative, recoveries⟩ :=
    FiniteMovingPatchFamily.canonicalNormalizedInteractionCoordinate_exists_uniform_transverse_recovery
  obtain ⟨initialRadius, initialPositive, initialConstant, initialOne, initials⟩ :=
    FiniteMovingPatchFamily.canonicalNormalizedInteractionCoordinate_exists_uniform_circle_bound
  obtain ⟨continuityRadius, continuityPositive, continuities⟩ :=
    FiniteMovingPatchFamily.canonicalNormalizedInteractionCoordinate_exists_uniform_raw_geometric_continuity
  obtain ⟨shiftRadius, shiftPositive, shifts⟩ :=
    FiniteMovingPatchFamily.canonicalExteriorAffineCoordinate_exists_uniform_shift_admissibility
      continuityRadius continuityPositive
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBounds, _⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds
  let radius := min (min slopeRadius recoveryRadius)
    (min (min initialRadius continuityRadius) (min shiftRadius (min inverseRadius (1 / 4))))
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have slopeLe : radius ≤ slopeRadius := (min_le_left _ _).trans (min_le_left _ _)
  have recoveryLe : radius ≤ recoveryRadius := (min_le_left _ _).trans (min_le_right _ _)
  have initialLe : radius ≤ initialRadius := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have continuityLe : radius ≤ continuityRadius := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have shiftLe : radius ≤ shiftRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have inverseLe : radius ≤ inverseRadius := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have quarterLe : radius ≤ 1 / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨radius, radiusPositive, ?_⟩
  intro forcingConstant terminal forcingNonnegative terminalNonnegative
  obtain ⟨bootstrapRoot, bootstrapEight, bootstrap⟩ :=
    EulerNonuniqueness.General.exists_uniform_quartic_observable_bootstrap_root
      (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf)
      forcingNonnegative (show 0 ≤ initialConstant by linarith) (show 0 ≤ slopeConstant by linarith)
      recoveryNonnegative lossNonnegative terminalNonnegative
  obtain ⟨scalarRoot, scalarEight, scalarBounds⟩ :=
    EulerNonuniqueness.General.exists_uniform_quartic_shape_confinement_root
      (forcingConstant := forcingConstant) (neutralConstant := 0) (shapeConstant := 1)
      (terminal := terminal) forcingNonnegative (by norm_num) (by norm_num) terminalNonnegative radiusPositive
  refine ⟨max bootstrapRoot scalarRoot, bootstrapEight.trans (le_max_left _ _), ?_⟩
  intro scaleRoot rootLarge count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon
    initial trajectory initialCircles initialClock marginPositive frequency distance weight mass frequencyLarge
    densityMagnitude weightScale ratioScale numeratorScale tube
  have rootBootstrap := (le_max_left _ _).trans rootLarge
  have rootScalar := (le_max_right _ _).trans rootLarge
  have rootPositive : 0 < scaleRoot := by linarith [bootstrapEight.trans rootBootstrap]
  let strength := fun index => scaleRoot ^ 3 * frequency index ^ 4
  let controlRadius := fun index => (forcingConstant + 1) / (scaleRoot ^ 2 * frequency index ^ 2)
  have scalar (index : Fin count) := scalarBounds scaleRoot rootScalar (frequency index) (weight index)
    (frequencyLarge index) (tube.weightNonnegative index) (weightScale index)
  have controlPositive (index : Fin count) : 0 < controlRadius index := (scalar index).1
  have controlOne (index : Fin count) : controlRadius index ≤ 1 := (scalar index).2.1
  have controlSmall (index : Fin count) : controlRadius index < radius := by
    simpa only [zero_mul, zero_add, one_mul] using (scalar index).2.2.2
  have primitiveBound (index : Fin count) : weight index / |configuration.density index| ≤ controlRadius index := by
    rw [densityMagnitude index]
    have bound := (scalar index).2.2.1
    linarith [controlPositive index]
  have primitiveSmall (index : Fin count) : weight index / |configuration.density index| ≤ radius :=
    (primitiveBound index).trans (controlSmall index).le
  have densityNonzero (index : Fin count) : configuration.density index ≠ 0 := by
    have frequencyPositive : 0 < frequency index := by linarith [frequencyLarge index]
    apply abs_pos.mp
    rw [densityMagnitude index]
    positivity
  have globalInside (current : ℝ) (inside : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [inside.1, trajectory.backward_positive], inside.2.trans_lt tube.beforeFinal⟩
  have shapeContinuous (index : Fin count) : Continuous (fun current => (trajectory.curve current).2.2 index) :=
    (continuous_apply index).comp (continuous_snd.comp (continuous_snd.comp trajectory.continuous))
  have coordinateContinuous (index : Fin count) (current : ℝ) (inside : current ∈ Icc 0 terminal) :
      ContinuousAt (trajectory.spectralCoordinate index) current := by
    have actual := ContinuousAt.comp (g := diskPhysicalSpectralCoordinate)
      (f := fun current => (trajectory.curve current).2.2 index)
      (inverseBounds _ ((tube.shapeSmall current inside index).le.trans inverseLe)).1.continuousAt
      (shapeContinuous index).continuousAt
    simpa only [spectralCoordinate, Function.comp_def] using actual
  have angularContinuous (index : Fin count) (current : ℝ) (inside : current ∈ Icc 0 terminal) :
      ContinuousAt (trajectory.contourAngular index) current :=
    diskNeutralCLM.continuous.continuousAt.comp (coordinateContinuous index current inside)
  have domainGap (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) :=
    trajectory.movingFamily.exterior_domain_gap_of_center_gaps index (tube.centerGaps current inside index)
  have smallFour (index : Fin count) : 4 * (trajectory.movingFamily.patch index).radius ≤ distance index :=
    by linarith [tube.small index, (trajectory.movingFamily.patch index).radius_positive]
  have smallFortyEight (index : Fin count) : 48 * (trajectory.movingFamily.patch index).radius ≤ distance index :=
    by linarith [tube.small index, (trajectory.movingFamily.patch index).radius_positive]
  have area (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) :=
    trajectory.shape_area_eq_pi_of_margin initialCircles marginPositive inside tube.beforeFinal tube.safe index
  have centered (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) :
      contourCentroidFunctional ((trajectory.curve current).2.2 index) = 0 := by
    rw [trajectory.contourCentroid_conserved (globalInside current inside) index, initialCircles index,
      contourCentroidFunctional_standardCircle_zero]
  have stationaryCentered (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) :
      contourCentroidFunctional (diskRelabelCurve (trajectory.contourAngular index current) 1) = 0 := by
    have half : ‖trajectory.contourAngular index current‖ < 1 / 2 :=
      ((tube.angularSmall current inside index).trans_le quarterLe).trans (by norm_num)
    rw [← fixedRelabelEquivalence_circle _ half (diskNeutralCLM_real _)]
    exact (contourCentroidFunctional_fixedRelabel _ half standardCircleBanach).trans
      contourCentroidFunctional_standardCircle_zero
  let controlled := fun index current => diskPhysicalTransverseProjection (trajectory.spectralCoordinate index current)
  let observable := trajectory.contourInteraction
  have controlledContinuous (index : Fin count) : ContinuousOn (controlled index) (Icc 0 terminal) := by
    intro current inside
    exact (diskPhysicalTransverseProjection.continuous.continuousAt.comp
      (coordinateContinuous index current inside)).continuousWithinAt
  have observableContinuous (index : Fin count) : ContinuousOn (observable index) (Icc 0 terminal) := by
    intro current inside
    have shifted := shifts trajectory.movingFamily index (trajectory.contourAngular index current)
      ((trajectory.curve current).2.2 index - diskRelabelCurve (trajectory.contourAngular index current) 1)
      ((tube.angularSmall current inside index).le.trans shiftLe) (diskNeutralCLM_real _)
      (densityNonzero index) (tube.distancePositive index) (tube.weightNonnegative index) (smallFour index)
      (domainGap current inside index) (tube.weightBound current inside index)
      ((tube.splitSmall current inside index).trans shiftLe) ((primitiveSmall index).trans shiftLe)
    have correctedSmall : ‖trajectory.movingFamily.canonicalExteriorAffineCoordinate index
        (trajectory.contourAngular index current) (configuration.density index) current
        ((trajectory.curve current).2.2 index) - standardCircleBanach‖ ≤ continuityRadius := by
      generalize coordinateEq : trajectory.movingFamily.canonicalExteriorAffineCoordinate index
        (trajectory.contourAngular index current) (configuration.density index) current = coordinate at shifted ⊢
      generalize baseEq : diskRelabelCurve (trajectory.contourAngular index current) 1 = base at shifted
      generalize dataEq : (trajectory.curve current).2.2 index = data at shifted ⊢
      rw [show base + (data - base) = data by abel] at shifted
      have triangle := norm_sub_le_norm_sub_add_norm_sub (coordinate data) data standardCircleBanach
      rw [norm_sub_rev _ data] at triangle
      linarith
    exact (continuities trajectory.movingFamily index
      ((tube.angularSmall current inside index).trans_le continuityLe) (angularContinuous index current inside)
      (shapeContinuous index).continuousAt (Filter.Eventually.of_forall (fun _ => diskNeutralCLM_real _))
      (densityNonzero index) (tube.distancePositive index) (smallFortyEight index)
      (fun source _ => tube.inside current inside source) (tube.centerGaps current inside index)
      correctedSmall).continuousWithinAt
  have initialBound (index : Fin count) : ‖observable index 0‖ ≤ initialConstant * (weight index / strength index) := by
    have initialInside : (0 : ℝ) ∈ Icc 0 terminal := ⟨le_rfl, terminalNonnegative⟩
    have actual := initials trajectory.movingFamily index (densityNonzero index) (tube.distancePositive index)
      (tube.weightNonnegative index) (smallFour index) (domainGap 0 initialInside index)
      (tube.weightBound 0 initialInside index) ((primitiveSmall index).trans initialLe)
    change ‖trajectory.contourInteraction index 0‖ ≤ _
    rw [trajectory.contourInteraction_initial_circle initialCircles index]
    generalize initialValueEq : trajectory.movingFamily.canonicalNormalizedInteractionCoordinate index
      0 (configuration.density index) 0 standardCircleBanach = initialValue at actual ⊢
    rw [densityMagnitude index] at actual
    exact actual
  have recovery (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) :
      ‖controlled index current‖ ≤ recoveryCoefficient * ‖observable index current‖ +
        recoveryLoss * (weight index / strength index) := by
    have actual := recoveries trajectory.movingFamily index (trajectory.contourAngular index current)
      ((trajectory.curve current).2.2 index) ((tube.angularSmall current inside index).le.trans recoveryLe)
      (diskNeutralCLM_real _) (densityNonzero index) (tube.distancePositive index) (tube.weightNonnegative index)
      (smallFour index) (domainGap current inside index) (tube.weightBound current inside index)
      ((tube.splitSmall current inside index).trans recoveryLe) ((primitiveSmall index).trans recoveryLe)
      (area current inside index) (centered current inside index)
    change ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate ((trajectory.curve current).2.2 index))‖ ≤
      recoveryCoefficient * ‖trajectory.movingFamily.canonicalNormalizedInteractionCoordinate index
        (trajectory.contourAngular index current) (configuration.density index) current
        ((trajectory.curve current).2.2 index)‖ + recoveryLoss * (weight index / strength index)
    generalize projectedEq : diskPhysicalTransverseProjection
      (diskPhysicalSpectralCoordinate ((trajectory.curve current).2.2 index)) = projected at actual ⊢
    generalize observedEq : trajectory.movingFamily.canonicalNormalizedInteractionCoordinate index
      (trajectory.contourAngular index current) (configuration.density index) current
      ((trajectory.curve current).2.2 index) = observed at actual ⊢
    rw [densityMagnitude index] at actual
    exact actual
  have prefixSlopes (base : ℝ) (baseInside : base ∈ Ico 0 terminal)
      (prefixBounds : ∀ current ∈ Icc 0 base, ∀ index, ‖controlled index current‖ ≤ controlRadius index)
      (index : Fin count) (threshold : ℝ)
      (strict : slopeConstant * (strength index * controlRadius index ^ 3 + weight index * controlRadius index ^ 2 +
        weight index * ((trajectory.movingFamily.patch index).radius / distance index) * controlRadius index +
        (weight index ^ 2 + mass index * weight index / distance index ^ 2) / strength index) < threshold) :
      ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖observable index current‖) base later < threshold := by
    have inside : base ∈ Icc 0 terminal := ⟨baseInside.1, baseInside.2.le⟩
    obtain ⟨neighborhood⟩ := tube.materialNear base baseInside index
    have actual := slopes trajectory initialCircles initialClock marginPositive terminal base (distance index)
      (weight index) (mass index) (controlRadius index) inside tube.beforeFinal tube.safe index
      (tube.distancePositive index) (tube.weightNonnegative index) (tube.massNonnegative index)
      (densityNonzero index) (tube.small index) (domainGap base inside index) (tube.weightBound base inside index)
      ((tube.shapeSmall base inside index).trans_le slopeLe) ((tube.angularSmall base inside index).le.trans slopeLe)
      ((tube.splitSmall base inside index).trans slopeLe) ((primitiveSmall index).trans slopeLe)
      (area base inside index) (centered base inside index)
      (prefixBounds base ⟨baseInside.1, le_rfl⟩ index) (primitiveBound index) (controlOne index)
      neighborhood.left neighborhood.right neighborhood.member neighborhood.inside neighborhood.material neighborhood.centered
      neighborhood.centerGaps neighborhood.weightBound neighborhood.massBound
      (tube.angularMember base inside index) (tube.relativeMember base inside index)
      ((centered base inside index).trans (stationaryCentered base inside index).symm)
    have actualStrict := strict
    dsimp only [strength] at actualStrict
    rw [← densityMagnitude index] at actualStrict
    exact (actual threshold actualStrict).frequently
  have confined := bootstrap scaleRoot rootBootstrap frequency weight
    (fun index => (trajectory.movingFamily.patch index).radius / distance index)
    (fun index => weight index ^ 2 + mass index * weight index / distance index ^ 2)
    frequencyLarge tube.weightNonnegative weightScale
    (fun index => div_nonneg (trajectory.movingFamily.patch index).radius_positive.le (tube.distancePositive index).le)
    ratioScale (fun index => by
      have weightNonnegative := tube.weightNonnegative index
      have massNonnegative := tube.massNonnegative index
      positivity) numeratorScale
    controlled observable controlledContinuous observableContinuous initialBound recovery prefixSlopes
  intro current inside index
  exact (confined current inside index).2

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
