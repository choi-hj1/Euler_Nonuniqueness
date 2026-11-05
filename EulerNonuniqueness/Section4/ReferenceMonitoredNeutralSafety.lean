import EulerNonuniqueness.Section4.ReferenceMonitoredMaterialPrefix
import EulerNonuniqueness.Section4.ReferenceNeutralPrefixSafety

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_monitored_neutral_improvement :
    ∃ memory ≥ (1 : ℝ), ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin backwardHorizon forwardHorizon initial)
      (scales : Scales),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ label, initial.2.2 label = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ {terminal shapeStop threshold : ℝ}, 0 < terminal → terminal ≤ 2 → terminal < forwardHorizon →
    0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
    shapeStop ≤ 1 / 48 →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
    ∀ {phase unstable : Fin count → ℝ},
    ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable threshold →
    (∀ current ∈ Icc 0 terminal, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor ≤ 0) →
    scales.strain ≤ 1 → scales.hessian ≤ 1 →
    (∀ index : Fin count, memory * scales.hessian * scales.length (index.val + 1) < 1 / 128) →
    ∀ current ∈ Icc 0 terminal, ∀ index,
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion current index‖ ≤
        memory * scales.hessian * scales.length (index.val + 1) ^ 2 ∧
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion current index‖ ≤
        memory * scales.length (index.val + 1) ^ 2 ∧
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion current index‖ < scales.length (index.val + 1) / 128 := by
  obtain ⟨memory, memoryOne, improvements⟩ := FiniteMovingPatchFamily.exists_uniform_reference_neutral_prefix_improvement
  refine ⟨memory, memoryOne, ?_⟩
  intro count configuration shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory scales
    densityIdentity radiusIdentity initialCircles initialClock marginPositive terminal shapeStop threshold terminalPositive terminalBound
    beforeFinal amplitudePositive frequencyLarge ratioLarge alphaPositive stopSmall lengthSmall radiusSmall phase unstable initialDisks
    closed strainSmall hessianSmall numerical
  have data := trajectory.reference_material_data_of_nonpositive_monitors scales densityIdentity radiusIdentity
    initialCircles initialClock marginPositive terminalPositive.le beforeFinal amplitudePositive (zero_lt_one.trans_le frequencyLarge)
    (by linarith) stopSmall lengthSmall radiusSmall closed
  have inside (current : ℝ) (member : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, member.1], member.2.trans_lt beforeFinal⟩
  have geometry (current : ℝ) (member : current ∈ Icc 0 terminal) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (closed current member)
  apply improvements trajectory.movingFamily scales densityIdentity data.1 terminalPositive terminalPositive.le terminalBound
    (Subset.refl _) amplitudePositive frequencyLarge ratioLarge alphaPositive initialDisks
    (fun current member _ => inside current member) data.2.2.2
    (fun current member index => ((geometry current member).2.1 index).1)
    (fun current member index => ((geometry current member).2.1 index).2.1)
    (fun current member index => ((geometry current member).2.1 index).2.2.2.1)
    (fun current member index => ((geometry current member).2.1 index).2.2.1)
    (fun current member receiver source different => ((geometry current member).2.2 receiver source different).1)
    lengthSmall data.2.2.1 ?_ strainSmall hessianSmall numerical
  intro index
  have positive := scales.radius_pos amplitudePositive (zero_lt_one.trans_le frequencyLarge) (by linarith) (index.val + 1)
  linarith [radiusSmall index, scales.length_pos (index.val + 1)]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
