import EulerNonuniqueness.Section4.ReferenceMonitoredCappedBootstrap
import EulerNonuniqueness.Section4.ReferenceMechanicalInitialMonitors
import EulerNonuniqueness.Section4.MovingReferenceGeometricShooting
import EulerNonuniqueness.Section4.ReferencePaperUnstableBootstrap

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] mechanicalMonitorHolderSpace mechanicalMonitorC1Space

local instance cappedMaterialShootingC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance cappedMaterialShootingC1AddGroup : AddCommGroup PeriodicC1HolderHalf :=
  cappedMaterialShootingC1Group.toAddCommGroup
local instance cappedMaterialShootingC1Sub : Sub PeriodicC1HolderHalf := cappedMaterialShootingC1AddGroup.toSub
local instance cappedMaterialShootingC1Zero : Zero PeriodicC1HolderHalf := cappedMaterialShootingC1AddGroup.toZero

theorem exists_uniform_capped_material_reference_shooting (requestedCap : ℝ) (requestedPositive : 0 < requestedCap) :
    ∃ monitor > 0, monitor ≤ requestedCap ∧ ∃ bootstrapBoundaryConstant ≥ (1 : ℝ), ∃ boundaryConstant ≥ (1 : ℝ),
    ∃ bootstrapMemory ≥ (1 : ℝ), ∃ memory ≥ (1 : ℝ), ∃ diagonalConstant ≥ (0 : ℝ),
    ∃ bootstrapInternal ≥ (0 : ℝ), ∃ bootstrapMoment > (0 : ℝ),
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ),
    ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
    ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
    ∀ shapeRadius : ℝ, 0 < shapeRadius → ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ReferenceMechanicalScaleBounds scales diagonalConstant bootstrapInternal bootstrapMemory
      (bootstrapBoundaryConstant / scaleRoot ^ 2) bootstrapMoment radius →
    ReferenceMechanicalScaleBounds scales diagonalConstant internal memory
      (boundaryConstant / scaleRoot ^ 2) momentRadius radius →
    ∀ {count : ℕ}, 0 < count → ∀ {configuration : FiniteContourConfiguration (count * 4)} {gap margin : ℝ},
    ∀ (phase : Fin count → ℝ)
      (trajectories : ∀ parameter : closedBall (0 : Fin count → ℝ) radius,
        MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3
          (referenceMechanicalInitialState scales phase parameter.val)),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    0 < margin → margin ≤ shapeRadius / 8 → margin ≤ 1 / 8 →
    (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second) →
    (∀ parameter : closedBall (0 : Fin count → ℝ) radius,
      ReferenceInitialDisks scales (trajectories parameter).movingFamily.patchMotion phase parameter.val (1 / 2)) →
    (∀ parameter : closedBall (0 : Fin count → ℝ) radius,
      2 * margin ≤ infDist (referenceMechanicalInitialState scales phase parameter.val)
      (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ) →
    Continuous (fun point : closedBall (0 : Fin count → ℝ) radius × ℝ => (trajectories point.1).curve point.2) →
    (∀ (parameter : closedBall (0 : Fin count → ℝ) radius) (current : ℝ), current ∈ Icc (0 : ℝ) 2 → ∀ label,
      ((trajectories parameter).curve current).2.2 label ∈ contourContinuousVectorSubmodule) →
    ∃ parameter : closedBall (0 : Fin count → ℝ) radius,
      FinitePatchEvolution scales (trajectories parameter).movingFamily.patchMotion 2 ∧
      (∀ current ∈ Icc (0 : ℝ) 2, ∀ index,
        |unstableShape (trajectories parameter).movingFamily.patchMotion current index| ≤ radius ∧
        |stableShape (trajectories parameter).movingFamily.patchMotion current index| ≤ radius) ∧
      (∀ current ∈ Icc (0 : ℝ) 2, ∀ index,
        referenceMechanicalMonitor configuration scales shapeRadius gap margin
          (referenceMechanicalShapeStop monitor shapeRadius) ((trajectories parameter).curve current) index < 0) ∧
      (∀ current ∈ Icc (0 : ℝ) 2, ∀ index patch,
        BoundaryCloseToCircle scales (trajectories parameter).movingFamily.patchMotion current index patch
          ((boundaryConstant / scaleRoot ^ 2) / scales.omega (index.val + 1) ^ 2)) := by
  obtain ⟨originalCap, originalCapPositive, boundaryConstant, boundaryOne, contourFactories⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_reference_contour_monitor_improvement_on_horizon
  let cap := min originalCap requestedCap
  have capPositive : 0 < cap := lt_min originalCapPositive requestedPositive
  obtain ⟨monitor, monitorPositive, monitorCap, bootstrapBoundaryConstant, bootstrapBoundaryOne,
    bootstrapMemory, bootstrapMemoryOne, diagonalConstant, diagonalNonnegative, bootstrapInternal, bootstrapInternalNonnegative,
    bootstrapMoment, bootstrapMomentPositive, bootstrapMaximum, bootstrapMaximumPositive, bootstrapMaximumSmall, bootstraps⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_reference_monitored_capped_bootstrap cap capPositive
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, shootingMaximum, shootingMaximumPositive,
    shootingMaximumSmall, shooting⟩ := exists_uniform_geometric_reference_shooting
  obtain ⟨memory, memoryOne, neutral⟩ :=
    MovingCentroidGaugeTrajectory.exists_uniform_reference_monitored_neutral_improvement
  refine ⟨monitor, monitorPositive, monitorCap.trans (min_le_right _ _), bootstrapBoundaryConstant, bootstrapBoundaryOne, boundaryConstant, boundaryOne,
    bootstrapMemory, bootstrapMemoryOne, memory, memoryOne, diagonalConstant, diagonalNonnegative,
    bootstrapInternal, bootstrapInternalNonnegative, bootstrapMoment, bootstrapMomentPositive,
    internal, internalNonnegative, momentRadius, momentPositive,
    min bootstrapMaximum shootingMaximum, lt_min bootstrapMaximumPositive shootingMaximumPositive,
    (min_le_right _ _).trans shootingMaximumSmall, ?_⟩
  intro radius radiusPositive radiusBound shapeRadius shapePositive
  obtain ⟨bootstrapRoot, bootstrapRootEight, bootstrap⟩ := bootstraps radius radiusPositive
    (radiusBound.trans (min_le_left _ _)) shapeRadius shapePositive
  obtain ⟨contourRoot, contourRootEight, contours⟩ := contourFactories 2 1 (by norm_num) (by norm_num)
  refine ⟨max bootstrapRoot contourRoot, bootstrapRootEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive bootstrapScales shootingScales
    count countPositive configuration gap margin phase trajectories densityIdentity radiusIdentity marginPositive marginShape marginUnit
    marginSlack initialDisks initialMargin jointContinuous shapeMember
  have rootBootstrap := (le_max_left _ _).trans rootLarge
  have rootContour := (le_max_right _ _).trans rootLarge
  have rootPositive : 0 < scaleRoot := by linarith [bootstrapRootEight.trans rootBootstrap]
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le bootstrapScales.frequencyLarge
  have ratioPositive : 0 < scales.ratio := by linarith
  have boundNonnegative : 0 ≤ boundaryConstant / scaleRoot ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have stopBounds := referenceMechanicalShapeStop_bounds monitorPositive shapePositive
  have parameterBound (parameter : closedBall (0 : Fin count → ℝ) radius) (index : Fin count) :
      |parameter.val index| ≤ radius := by
    have total : ‖parameter.val‖ ≤ radius := by simpa only [mem_closedBall, dist_zero_right] using parameter.property
    exact (show |parameter.val index| ≤ ‖parameter.val‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm parameter.val index).trans total
  have radiusSmall (index : Fin count) : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000 := by
    linarith [bootstrapScales.radiusSmall (index.val + 1),
      scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
  have initialStrict (parameter : closedBall (0 : Fin count → ℝ) radius) :=
    referenceMechanicalMonitor_initial_strict configuration scales phase parameter.val marginPositive stopBounds.1
      (radiusBound.trans ((min_le_left _ _).trans bootstrapMaximumSmall)) (parameterBound parameter)
      (fun index => bootstrapScales.lengthSmall (index.val + 1)) (initialMargin parameter)
  have initialCoordinates (parameter : closedBall (0 : Fin count → ℝ) radius) (index : Fin count) :
      (movingReferenceShapeCoordinates scales ((trajectories parameter).curve 0) index).1 = parameter.val index := by
    rw [(trajectories parameter).initial_identity]
    exact congrArg Prod.fst (movingReferenceShapeCoordinates_initial scales phase parameter.val
      (fun label => (parameterBound parameter label).trans (by linarith [radiusBound.trans ((min_le_right _ _).trans shootingMaximumSmall)])) index)
  let deformation := fun (_ : closedBall (0 : Fin count → ℝ) radius) (_ : ℝ) (index : Fin count) =>
    (boundaryConstant / scaleRoot ^ 2) / scales.omega (index.val + 1) ^ 2
  suffices selected : ∃ parameter : closedBall (0 : Fin count → ℝ) radius,
      FinitePatchEvolution scales (trajectories parameter).movingFamily.patchMotion 2 ∧
      ∀ current ∈ Icc (0 : ℝ) 2, ∀ index,
        |unstableShape (trajectories parameter).movingFamily.patchMotion current index| ≤ radius ∧
        |stableShape (trajectories parameter).movingFamily.patchMotion current index| ≤ radius by
    obtain ⟨parameter, evolution, paperBound⟩ := selected
    have monitored := (trajectories parameter).reference_monitors_confined_of_paper_unstable_bound scales
      (fun _ => rfl) (by norm_num : (2 : ℝ) < 3) (initialStrict parameter)
      (by
        intro terminal terminalInside prefixBound
        exact bootstrap scales scaleRoot rootBootstrap amplitudeIdentity ratioLarge alphaPositive bootstrapScales
          countPositive (trajectories parameter) densityIdentity radiusIdentity (fun _ => rfl) rfl marginPositive marginShape marginUnit
          marginSlack (initialDisks parameter) (parameterBound parameter) (initialStrict parameter)
          terminal terminalInside.1 terminalInside.2
          (fun current member label => shapeMember parameter current ⟨member.1, member.2.trans terminalInside.2⟩ label) prefixBound)
      (fun current member index => (paperBound current member index).1)
    have closed (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) (index : ReferenceMechanicalIndex count) :=
      (monitored current member index).le
    have data := (trajectories parameter).reference_material_data_of_nonpositive_monitors scales densityIdentity radiusIdentity
      (fun _ => rfl) rfl marginPositive (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 3)
      amplitudePositive frequencyPositive ratioPositive stopBounds.2.2.2
      (fun index => bootstrapScales.lengthSmall (index.val + 1)) radiusSmall closed
    have actualContours := contours scales scaleRoot rootContour 2 (by norm_num) le_rfl amplitudeIdentity
      bootstrapScales.frequencyLarge ratioLarge alphaPositive bootstrapScales.strainSmall (trajectories parameter)
      densityIdentity radiusIdentity (fun _ => rfl) rfl marginPositive (by norm_num : (2 : ℝ) < 3)
      (fun current member => referenceMechanicalMonitor_clearance (closed current member .clearance))
      (fun current member => referenceMechanicalMonitor_strict_clearance (monitored current ⟨member.1, member.2.le⟩ .clearance))
      data.2.1
      (fun current member label =>
        ((referenceMechanicalMonitor_shape label (closed current member (.shape label))).trans_lt stopBounds.2.1).trans_le (monitorCap.trans (min_le_left _ _)))
      (fun current member label => shapeMember parameter current member label)
    refine ⟨parameter, evolution, paperBound, monitored, ?_⟩
    intro current member index patch
    simpa only [div_div] using actualContours.2 current member index patch
  apply shooting radius radiusPositive (radiusBound.trans (min_le_right _ _)) scales phase
    (fun parameter => referenceMechanicalInitialState scales phase parameter.val) trajectories densityIdentity radiusIdentity
    (fun _ _ => rfl) initialDisks marginPositive (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 3)
    amplitudePositive bootstrapScales.frequencyLarge ratioLarge alphaPositive jointContinuous initialCoordinates
    memory (boundaryConstant / scaleRoot ^ 2) (by linarith) boundNonnegative shootingScales.hessianSmall
    (fun index => scales.length_le_one frequencyPositive ratioPositive (index.val + 1))
    (fun index => shootingScales.momentSmall (index.val + 1))
    (fun index => shootingScales.forcingSmall (index.val + 1)) deformation
  intro parameter terminal terminalInside prefixBound
  have beforeFinal : terminal < 3 := by linarith [terminalInside.2]
  have monitored := bootstrap scales scaleRoot rootBootstrap amplitudeIdentity ratioLarge alphaPositive bootstrapScales
    countPositive (trajectories parameter) densityIdentity radiusIdentity (fun _ => rfl) rfl marginPositive marginShape marginUnit
    marginSlack (initialDisks parameter) (parameterBound parameter) (initialStrict parameter)
    terminal terminalInside.1 terminalInside.2
    (fun current member label => shapeMember parameter current ⟨member.1, member.2.trans terminalInside.2⟩ label) prefixBound
  have closed (current : ℝ) (member : current ∈ Icc 0 terminal) (index : ReferenceMechanicalIndex count) :=
    (monitored current member index).le
  have data := (trajectories parameter).reference_material_data_of_nonpositive_monitors scales densityIdentity radiusIdentity
    (fun _ => rfl) rfl marginPositive terminalInside.1 beforeFinal amplitudePositive frequencyPositive ratioPositive
    stopBounds.2.2.2 (fun index => bootstrapScales.lengthSmall (index.val + 1)) radiusSmall closed
  have inside (current : ℝ) (member : current ∈ Icc 0 terminal) : current ∈ Ioo (-1 : ℝ) 3 := by
    constructor <;> linarith [member.1, member.2]
  have decoded (current : ℝ) (member : current ∈ Icc 0 terminal) :=
    (trajectories parameter).reference_paper_geometry_of_nonpositive_monitors scales (fun _ => rfl)
      (inside current member) (closed current member)
  have actualContours := contours scales scaleRoot rootContour terminal terminalInside.1 terminalInside.2 amplitudeIdentity
    bootstrapScales.frequencyLarge ratioLarge alphaPositive bootstrapScales.strainSmall (trajectories parameter)
    densityIdentity radiusIdentity (fun _ => rfl) rfl marginPositive beforeFinal
    (fun current member => (decoded current member).1)
    (fun current member => referenceMechanicalMonitor_strict_clearance (monitored current ⟨member.1, member.2.le⟩ .clearance))
    (fun current member index => (data.2.1 current member index))
    (fun current member label =>
      ((referenceMechanicalMonitor_shape label (closed current member (.shape label))).trans_lt stopBounds.2.1).trans_le
        (monitorCap.trans (min_le_left _ _)))
    (fun current member label => shapeMember parameter current ⟨member.1, member.2.trans terminalInside.2⟩ label)
  have momentBound : ∀ current ∈ Icc 0 terminal, ∀ index,
      ‖centroidAsymmetry (trajectories parameter).movingFamily.patchMotion current index‖ ≤
        memory * scales.length (index.val + 1) ^ 2 := by
    by_cases terminalZero : terminal = 0
    · intro current member index
      have currentZero : current = 0 := by linarith [member.1, member.2]
      have initialValue := data.1.reference_initial_center_and_asymmetry terminalInside.1 amplitudePositive frequencyPositive
        ratioPositive (initialDisks parameter) index
      rw [currentZero, initialValue.2, norm_zero]
      positivity
    · have positive : 0 < terminal := lt_of_le_of_ne terminalInside.1 (Ne.symm terminalZero)
      have actual := neutral (trajectories parameter) scales densityIdentity radiusIdentity (fun _ => rfl) rfl marginPositive
        positive terminalInside.2 beforeFinal amplitudePositive bootstrapScales.frequencyLarge ratioLarge alphaPositive
        stopBounds.2.2.2 (fun index => bootstrapScales.lengthSmall (index.val + 1)) radiusSmall (initialDisks parameter)
        closed shootingScales.strainSmall shootingScales.hessianSmall (fun index => shootingScales.neutralSmall (index.val + 1))
      exact fun current member index => (actual current member index).2.1
  refine ⟨fun current member => (decoded current member).1, ?_⟩
  intro current member index
  refine ⟨data.2.1 current member index, ?_, ?_, shootingScales.deformationSmall (index.val + 1), le_rfl,
    ((decoded current member).2.1 index).1, ((decoded current member).2.1 index).2.1, momentBound current member index⟩
  · intro patch
    simpa only [deformation, div_div] using actualContours.2 current member index patch
  · exact div_nonneg boundNonnegative (sq_nonneg _)

end EulerNonuniqueness.Paper

