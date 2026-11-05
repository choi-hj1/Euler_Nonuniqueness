import EulerNonuniqueness.Section5.CascadeTerminalFinerInitialData
import EulerNonuniqueness.Section5.CascadeNormalizedPointEquation

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

/-- Physical information retained across stages; no stage chart or FULL state is shared. -/
structure CascadePhysicalStageData
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (index : Fin count)
    (incomingTime extent magnitude coefficient error phaseTolerance timingTolerance matchingTolerance : ℝ) where
  entry : ℝ
  entryInside : entry ∈ Icc 0 path.stop
  firstSeparation : FirstSeparationTime scales orbit sectionTime
    prepared.trajectory.movingFamily.patchMotion index entry
  direction : ℂ
  directionNorm : ‖direction‖ = 1
  outgoingPhase : ℝ
  directionPhase : direction = Complex.exp (Complex.I * (outgoingPhase : ℂ))
  firstError : ‖firstDipoleSeparation prepared.trajectory.movingFamily.patchMotion entry index -
    (scales.length (index.val + 1) : ℂ) * direction‖ ≤ error * scales.length (index.val + 1)
  secondError : ‖secondDipoleSeparation prepared.trajectory.movingFamily.patchMotion entry index -
    (scales.length (index.val + 1) : ℂ) * (-direction)‖ ≤ error * scales.length (index.val + 1)
  outgoingProjection : (3 / 4 : ℝ) * scales.length (index.val + 1) * separationRadius orbit sectionTime ≤
    (Complex.I * star direction * (firstDipoleCenter prepared.trajectory.movingFamily.patchMotion entry index -
      secondDipoleCenter prepared.trajectory.movingFamily.patchMotion entry index)).re
  centerUpper : ‖firstDipoleCenter prepared.trajectory.movingFamily.patchMotion entry index -
    secondDipoleCenter prepared.trajectory.movingFamily.patchMotion entry index‖ ≤
      (5 / 4 : ℝ) * scales.length (index.val + 1) * separationRadius orbit sectionTime
  extents : ∀ time ∈ Icc 0 entry, ∀ patch : Fin 4,
    ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤ extent * scales.length (index.val + 1) ∧
    ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
      quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤ extent * scales.length (index.val + 1)
  domains : ∀ time ∈ Icc 0 entry, ∀ patch : Fin 4,
    prepared.trajectory.movingFamily.patchMotion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
        (extent * scales.length (index.val + 1)) ∧
    prepared.referenceWitness.trajectory.movingFamily.patchMotion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index)
        (extent * scales.length (index.val + 1))
  sharp : ∀ time ∈ Icc 0 entry,
    prepared.rawSourceCenteredState time index +
      ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖ +
      ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index - quadrupoleCenter prepared.reference time index‖ /
        scales.location (index.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
      magnitude * Real.exp (coefficient * scales.omega (index.val + 1) * (time - entry))
  winding : ℤ
  wrappedPhase : |outgoingPhase - dipoleAngle (index.val + 1) +
    scales.omega (index.val + 1) * (entry - scales.predictedTime sectionTime count (index.val + 1)) -
      (winding : ℝ) * Real.pi| ≤ phaseTolerance
  timing : |scales.omega (index.val + 1) *
    (entry - scales.predictedTime sectionTime count (index.val + 1))| ≤ timingTolerance
  previousMatch : index.val + 1 < count → ∃ hit ∈ Icc 0 entry, ∃ rotation : ℂ,
    ‖rotation‖ = 1 ∧
    ‖cascadeNormalizedPointPositions scales prepared.trajectory.movingFamily.patchMotion index hit rotation 0 -
      centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ matchingTolerance

theorem eventually_actual_terminal_physical_stage_data
    (orbit : SeparatingOrbit) (sectionTime incomingTime error : ℝ)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
    (extent magnitude coefficient phaseTolerance timingTolerance matchingTolerance : ℝ)
    (extentLarge : max 4 (max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖) + 1) ≤ extent)
    (magnitudeLarge : max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖) + 2 ≤ magnitude)
    (phaseNonnegative : 0 ≤ phaseTolerance) (timingNonnegative : 0 ≤ timingTolerance) :
    ∀ scales : Scales, 0 < scales.amplitude → 128 ≤ scales.ratio → 0 < scales.alpha →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, 2 ≤ count → ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, threshold ≤ 1 / 2 →
    ∀ index : Fin count, index.val + 1 = count →
    ∃ data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance,
      data.entry = 0 ∧ data.direction = Complex.exp (Complex.I * (dipoleAngle count : ℂ)) ∧
        data.outgoingPhase = dipoleAngle count ∧ data.winding = 0 := by
  intro scales amplitudePositive ratioLarge alphaPositive
  have ratioBound : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 128).trans ratioLarge
  filter_upwards [eventually_actual_terminal_finer_initial_data orbit sectionTime error errorNonnegative
      errorSmall radiusLarge separationClose outgoing scales amplitudePositive ratioLarge alphaPositive,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with frequency initial geometry frequencyPositive
  intro count countLarge phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap
    prepared path thresholdSmall index terminal
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let receiver : Fin count := ⟨count - 2, by omega⟩
  have adjacent : receiver.val + 1 = index.val := by dsimp [receiver]; omega
  have finer : receiver.val < index.val := by omega
  have data := initial count phase dipoleAngle prepared path thresholdSmall receiver index adjacent terminal
  dsimp only at data
  have geometryInitial := data.2.2.1 index finer
  have extentsInitial := data.2.2.2.1 index finer 0 (by constructor <;> norm_num)
  have sharpInitial := data.2.2.2.2.1 index finer 0 (by constructor <;> norm_num)
  have domainInitial := data.2.2.2.2.2.1 index finer 0 (by constructor <;> norm_num)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  let positions := relabelNegativePoints (fun patch => patchCentroid motion 0 index patch)
  let rotation := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ))
  let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
  have positionsIdentity : positions = fun target => (changed.location count : ℂ) +
      (changed.length count : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target := by
    funext target
    dsimp only [positions, relabelNegativePoints]
    rw [path.evolution.cascade_terminal_initial_centroid path.stopPositive.le amplitudePositive frequencyPositive
      ratioPositive prepared.commonInitial index terminal, separatingInitialCenter_eq_physical_orbit]
    simp [physicalSeparatingPointOrbit, rotation, negativeLabelSwap, changed]
  have close : ‖positions - (fun target => (changed.location count : ℂ) +
      (changed.length count : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target)‖ ≤
      error * changed.length count / 4 := by
    rw [positionsIdentity, sub_self, norm_zero]
    exact div_nonneg (mul_nonneg errorNonnegative (changed.length_pos count).le) (by norm_num)
  have outgoingInitial := physical_outgoing_initial_data (positive := orbit.positive sectionTime)
    (negative := orbit.negative sectionTime) (direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)))
    (rotation := rotation) (center := (changed.location count : ℂ)) (positions := positions)
    (changed.length_pos count) errorNonnegative errorSmall
    (by simp [Complex.norm_exp, Complex.mul_re]) (by simp [rotation, Complex.norm_exp, Complex.mul_re])
    ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) separationClose outgoing close
  have directionIdentity : rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)) = direction := by
    dsimp only [rotation, direction]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [directionIdentity] at outgoingInitial
  have firstInitial : ‖firstDipoleSeparation motion 0 index - (changed.length (index.val + 1) : ℂ) * direction‖ ≤
      error * changed.length (index.val + 1) := by
    simpa [firstDipoleSeparation, positions, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      terminal] using outgoingInitial.1
  have secondInitial : ‖secondDipoleSeparation motion 0 index - (changed.length (index.val + 1) : ℂ) * (-direction)‖ ≤
      error * changed.length (index.val + 1) := by
    simpa [secondDipoleSeparation, positions, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      terminal] using outgoingInitial.2.1
  have referenceData := prepared.referenceWitness.evolution.reference_initial_center_and_asymmetry
    (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial index
  have referenceExtent (patch : Fin 4) :
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index‖ ≤
      2 * changed.length (index.val + 1) := by
    rw [referenceData.1, prepared.referenceWitness.evolution.reference_initial_centroid
      (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial index patch]
    exact initialDiskCenter_offset_bound changed _ _ _ ((prepared.referenceWitness.initial index).1.trans thresholdSmall) patch
  have extentFour : 4 ≤ extent := (le_max_left _ _).trans extentLarge
  have referenceDomain (patch : Fin 4) : prepared.referenceWitness.trajectory.movingFamily.patchMotion.domain 0 index patch ⊆
      Metric.closedBall (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index)
        (extent * changed.length (index.val + 1)) := by
    intro position member
    have domain := prepared.referenceWitness.trajectory.domain_subset_centroid_ball changed prepared.referenceWitness.radiusIdentity
      (fun _ => rfl) (by constructor <;> norm_num) index patch member
    rw [Metric.mem_closedBall, dist_eq_norm] at domain ⊢
    have triangle := norm_sub_le_norm_sub_add_norm_sub position
      (patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index patch)
      (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index)
    have radiusBound := (geometry (index.val + 1)).2.1
    change changed.radius (index.val + 1) ≤ 1 * changed.length (index.val + 1) / 1000 at radiusBound
    change ‖position - patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 index patch‖ ≤
      2 * changed.radius (index.val + 1) at domain
    nlinarith only [triangle, domain, referenceExtent patch, radiusBound, lengthPositive,
      mul_le_mul_of_nonneg_right extentFour lengthPositive.le]
  refine ⟨{
    entry := 0
    entryInside := ⟨le_rfl, path.stopPositive.le⟩
    firstSeparation := path.evolution.cascade_terminal_firstSeparationTime path.stopPositive.le
      amplitudePositive frequencyPositive ratioPositive prepared.commonInitial index terminal
    direction := direction
    directionNorm := geometryInitial.2.2.2.2.1
    outgoingPhase := dipoleAngle count
    directionPhase := rfl
    firstError := firstInitial
    secondError := secondInitial
    outgoingProjection := geometryInitial.2.2.2.2.2.2.2.1
    centerUpper := geometryInitial.2.2.2.2.2.2.2.2
    extents := ?_
    domains := ?_
    sharp := ?_
    winding := 0
    wrappedPhase := ?_
    timing := ?_
    previousMatch := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro time inside patch
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    exact ⟨(extentsInitial.2 patch).trans (mul_le_mul_of_nonneg_right extentLarge lengthPositive.le),
      (extentsInitial.1 patch).trans (mul_le_mul_of_nonneg_right extentLarge lengthPositive.le)⟩
  · intro time inside patch
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    refine ⟨?_, referenceDomain patch⟩
    exact (domainInitial patch).trans (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right extentLarge lengthPositive.le))
  · intro time inside
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at sharpInitial ⊢
    exact sharpInitial.trans magnitudeLarge
  · simpa [terminal, Scales.predictedTime] using phaseNonnegative
  · simpa [terminal, Scales.predictedTime] using timingNonnegative
  · intro nonterminal
    omega

end EulerNonuniqueness.Paper
