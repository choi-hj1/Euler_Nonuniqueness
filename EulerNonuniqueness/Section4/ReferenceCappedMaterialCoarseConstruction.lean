import EulerNonuniqueness.Section4.ReferenceControlledShootingFamilies
import EulerNonuniqueness.Section4.ReferenceCappedMaterialShooting
import EulerNonuniqueness.Section4.ReferenceMonitoredCoarseBounds
import EulerNonuniqueness.Section4.ReferenceBoundMonotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import EulerNonuniqueness.Section4.ReferenceMaterialWitness

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_capped_material_coarse_construction
    (requestedCap : ℝ) (requestedPositive : 0 < requestedCap)
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (ratioLarge : 2 ≤ ratio) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ constant > (0 : ℝ),
    ∀ threshold : ℝ, 0 < threshold → threshold ≤ thresholdMax →
    ∃ amplitudeMin > (0 : ℝ), ∀ amplitude : ℝ, amplitudeMin ≤ amplitude →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, 0 < count → ∀ phase : Fin count → ℝ,
    ∃ witness : ReferenceMaterialCoarseWitness ⟨alpha, amplitude, ratio, frequency⟩ phase threshold constant,
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ label,
        ‖(witness.trajectory.curve time).2.2 label - standardCircleBanach‖ < requestedCap := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, controlledFamilies⟩ :=
    exists_uniform_controlled_reference_shooting_families
  obtain ⟨monitor, monitorPositive, monitorRequested, bootstrapBoundary, bootstrapBoundaryOne, boundary, boundaryOne,
    bootstrapMemory, bootstrapMemoryOne, memory, memoryOne, diagonalConstant, diagonalNonnegative,
    bootstrapInternal, bootstrapInternalNonnegative, bootstrapMoment, bootstrapMomentPositive,
    internal, internalNonnegative, momentRadius, momentPositive,
    maximumRadius, maximumPositive, maximumSmall, shootingFamilies⟩ :=
    exists_uniform_capped_material_reference_shooting requestedCap requestedPositive
  have boundaryNonnegative : 0 ≤ boundary := by linarith
  have uniformBoundNonnegative : 0 ≤ boundary / 64 := by positivity
  refine ⟨maximumRadius, maximumPositive, maximumSmall,
    referenceCoarseBoundConstant (boundary / 64),
    (referenceCoarseBoundConstant_bounds uniformBoundNonnegative).1, ?_⟩
  intro threshold thresholdPositive thresholdBound
  obtain ⟨rootMin, rootEight, shooting⟩ :=
    shootingFamilies threshold thresholdPositive thresholdBound shapeRadius shapePositive
  have rootMinPositive : 0 < rootMin := by linarith
  refine ⟨rootMin ^ 3, by positivity, ?_⟩
  intro amplitude amplitudeLarge
  have amplitudePositive : 0 < amplitude := (by positivity : 0 < rootMin ^ 3).trans_le amplitudeLarge
  let scaleRoot := amplitude ^ ((3 : ℝ)⁻¹)
  have rootPositive : 0 < scaleRoot := Real.rpow_pos_of_pos amplitudePositive _
  have cube : scaleRoot ^ 3 = amplitude :=
    Real.rpow_inv_natCast_pow amplitudePositive.le (by norm_num : (3 : ℕ) ≠ 0)
  have rootLarge : rootMin ≤ scaleRoot := by
    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rwa [cube]
  let scales : Scales := ⟨alpha, amplitude, ratio, 0⟩
  have bootstrapBoundNonnegative : 0 ≤ bootstrapBoundary / scaleRoot ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have boundNonnegative : 0 ≤ boundary / scaleRoot ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have bootstrapBounds := scales.eventually_reference_mechanical_scale_bounds
    amplitudePositive ratioLarge alphaPositive (diagonalConstant := diagonalConstant)
    bootstrapInternalNonnegative bootstrapMemoryOne bootstrapBoundNonnegative bootstrapMomentPositive thresholdPositive
  have shootingBounds := scales.eventually_reference_mechanical_scale_bounds
    amplitudePositive ratioLarge alphaPositive (diagonalConstant := diagonalConstant)
    internalNonnegative memoryOne boundNonnegative momentPositive thresholdPositive
  filter_upwards [bootstrapBounds, shootingBounds] with frequency bootstrapScales shootingScales
  intro count countPositive phase
  let currentScales : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < currentScales.frequency := zero_lt_one.trans_le bootstrapScales.frequencyLarge
  have ratioPositive : 0 < currentScales.ratio := by change 0 < ratio; linarith
  have lengthSmall (index : Fin count) :
      currentScales.length (index.val + 1) ≤ currentScales.location (index.val + 1) / 1000 :=
    bootstrapScales.lengthSmall (index.val + 1)
  have radiusSmall (index : Fin count) :
      currentScales.radius (index.val + 1) ≤ currentScales.length (index.val + 1) / 1000 := by
    have radiusPositive := currentScales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
    linarith [bootstrapScales.radiusSmall (index.val + 1)]
  obtain ⟨configuration, densityIdentity, radiusIdentity, gap, _, margin, marginPositive,
    marginShape, marginUnit, marginSlack, trajectories, initialDisks, initialMargin,
    jointContinuous, shapeMember⟩ := controlledFamilies count countPositive currentScales
      amplitudePositive frequencyPositive ratioPositive lengthSmall radiusSmall phase threshold thresholdPositive
      (by linarith [thresholdBound.trans maximumSmall])
  obtain ⟨parameter, evolution, shapeBounds, monitored, boundaryBounds⟩ :=
    shooting currentScales scaleRoot rootLarge cube.symm ratioLarge alphaPositive bootstrapScales shootingScales
      countPositive phase trajectories densityIdentity radiusIdentity marginPositive marginShape marginUnit marginSlack
      initialDisks initialMargin jointContinuous shapeMember
  have stopSmall := (referenceMechanicalShapeStop_bounds monitorPositive shapePositive).2.2.2
  have coarse := (trajectories parameter).referenceCoarseBounds_of_monitors_and_shape_confinement currentScales
    densityIdentity radiusIdentity (fun _ => rfl) rfl marginPositive amplitudePositive
    bootstrapScales.frequencyLarge ratioLarge alphaPositive stopSmall boundNonnegative lengthSmall radiusSmall
    (initialDisks parameter) (fun current member index => (monitored current member index).le) shapeBounds boundaryBounds
  have boundUniform : boundary / scaleRoot ^ 2 ≤ boundary / 64 :=
    div_le_div_of_nonneg_left boundaryNonnegative (by norm_num) (by nlinarith [rootEight.trans rootLarge])
  have constantOrdered : referenceCoarseBoundConstant (boundary / scaleRoot ^ 2) ≤
      referenceCoarseBoundConstant (boundary / 64) := by
    dsimp only [referenceCoarseBoundConstant]
    linarith
  have strainNonnegative : 0 ≤ currentScales.strain := tsum_nonneg fun source =>
    div_nonneg (currentScales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ currentScales.hessian := tsum_nonneg fun source =>
    div_nonneg (currentScales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (currentScales.location_pos _).le _)
  have uniformCoarse := coarse.mono_constant
    (referenceCoarseBoundConstant_bounds boundNonnegative).1.le constantOrdered strainNonnegative hessianNonnegative
  refine ⟨{
    unstable := parameter.val
    configuration := configuration
    densityIdentity := densityIdentity
    radiusIdentity := radiusIdentity
    shapeRadius := shapeRadius
    shapePositive := shapePositive
    shapeSmall := shapeSmall
    gap := gap
    margin := margin
    marginPositive := marginPositive
    trajectory := trajectories parameter
    initial := ?_
    evolution := evolution
    coarse := uniformCoarse
    safe := ?_
    continuousVectors := shapeMember parameter
  }, ?_⟩
  · intro index
    have total : ‖parameter.val‖ ≤ threshold := by
      simpa only [mem_closedBall, dist_zero_right] using parameter.property
    refine ⟨(show |parameter.val index| ≤ ‖parameter.val‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm parameter.val index).trans total,
      (initialDisks parameter index).2⟩
  · intro time inside
    have clearance := monitored time inside (.clearance)
    change margin - infDist ((trajectories parameter).curve time)
      (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ < 0 at clearance
    linarith
  · intro time inside label
    have estimate := monitored time inside (.shape label)
    change ‖((trajectories parameter).curve time).2.2 label - standardCircleBanach‖ -
      referenceMechanicalShapeStop monitor shapeRadius < 0 at estimate
    exact (sub_neg.mp estimate).trans_le
      ((referenceMechanicalShapeStop_bounds monitorPositive shapePositive).2.1.le.trans monitorRequested)

end EulerNonuniqueness.Paper


