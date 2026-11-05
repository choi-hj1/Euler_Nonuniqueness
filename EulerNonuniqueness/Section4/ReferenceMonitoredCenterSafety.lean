import EulerNonuniqueness.Section4.ReferenceMonitoredMaterialPrefix
import EulerNonuniqueness.Section4.ReferenceAbsoluteCenterSafety
import EulerNonuniqueness.Section4.ReferencePairwiseSafety

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem reference_center_monitors_strict_of_nonpositive_prefix
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach) (initialClock : initial.1 = 0)
    (marginPositive : 0 < margin) {terminal shapeStop tolerance threshold : ℝ}
    (terminalNonnegative : 0 ≤ terminal) (terminalBound : terminal ≤ 2) (beforeFinal : terminal < forwardHorizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (stopSmall : shapeStop ≤ 1 / 48)
    {phase unstable : Fin count → ℝ}
    (initialDisks : ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable threshold)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤ scales.length (index.val + 1) / 1000)
    (toleranceNonnegative : 0 ≤ tolerance)
    (omegaLength : ∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤
      tolerance * scales.location (index.val + 1))
    (pairBudget : 2 * ((15120 / Real.pi) * scales.strain + 1800 * tolerance) ≤ 1 / 4)
    (absoluteBudget : 2 * (600 * tolerance + (3456 / Real.pi) * scales.strain +
      (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1)) ≤ 1 / 2)
    (bounds : ∀ current ∈ Icc 0 terminal, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor ≤ 0) :
    (∀ current ∈ Icc 0 terminal, ∀ receiver source : Fin count,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) (.pair receiver source) < 0) ∧
    (∀ current ∈ Icc 0 terminal, ∀ label : Fin (count * 4),
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) (.center label) < 0) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have radiusBound (index : Fin count) : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000 := by
    have nonnegative := (scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)).le
    have estimate := radiusSmall index
    nlinarith
  obtain ⟨evolution, geometry, boundary, material⟩ := trajectory.reference_material_data_of_nonpositive_monitors scales
    densityIdentity radiusIdentity initialCircles initialClock marginPositive terminalNonnegative beforeFinal amplitudePositive
    frequencyPositive ratioPositive stopSmall lengthSmall radiusBound bounds
  have inside (current : ℝ) (member : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, member.1], member.2.trans_lt beforeFinal⟩
  have decoded (current : ℝ) (member : current ∈ Icc 0 terminal) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (bounds current member)
  have pairEstimate := trajectory.movingFamily.reference_pair_center_change_bound scales densityIdentity evolution
    terminalNonnegative (Subset.refl _) amplitudePositive frequencyBound ratioBound alphaPositive initialDisks
    (fun current member _ => inside current member) material
    (fun current member index => ((decoded current member).2.1 index).1)
    (fun current member index => ((decoded current member).2.1 index).2.1)
    (fun current member index => ((decoded current member).2.1 index).2.2.2.1)
    (fun current member index => ((decoded current member).2.1 index).2.2.1)
    (fun current member receiver source different => ((decoded current member).2.2 receiver source different).1)
    (fun current member receiver source different => ((decoded current member).2.2 receiver source different).2)
    lengthSmall boundary (by norm_num) (by exact le_rfl) radiusSmall toleranceNonnegative omegaLength
  have absoluteOmega (index : Fin count) : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ tolerance :=
    (omegaLength index).trans (mul_le_of_le_one_right toleranceNonnegative (scales.location_le_one _))
  have absoluteEstimate := trajectory.movingFamily.reference_absolute_center_change_bound scales densityIdentity evolution
    terminalNonnegative (Subset.refl _) amplitudePositive frequencyBound ratioBound alphaPositive initialDisks
    (fun current member _ => inside current member) material
    (fun current member index => ((decoded current member).2.1 index).1)
    (fun current member index => ((decoded current member).2.1 index).2.1)
    (fun current member index => ((decoded current member).2.1 index).2.2.2.1)
    (fun current member index => ((decoded current member).2.1 index).2.2.1)
    (fun current member receiver source different => ((decoded current member).2.2 receiver source different).1)
    lengthSmall boundary (by norm_num) (by exact le_rfl) radiusSmall absoluteOmega
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have velocityNonnegative : 0 ≤ ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) :=
    tsum_nonneg fun source => div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (scales.location_pos _).le
  have pairNonnegative : 0 ≤ (15120 / Real.pi) * scales.strain + 1800 * tolerance := by positivity
  have absoluteNonnegative : 0 ≤ 600 * tolerance + (3456 / Real.pi) * scales.strain +
      (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1) := by positivity
  constructor
  · intro current member receiver source
    by_cases same : receiver = source
    · simp only [referenceMechanicalMonitor, same, if_true]
      norm_num
    · have gapPositive : 0 < |scales.location (receiver.val + 1) - scales.location (source.val + 1)| :=
        scales.location_distance_pos (fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
      have estimate := pairEstimate current member receiver source same
      have geometricReceiver := trajectory.movingReferenceGeometricObservables_eq_paper initialCircles (inside current member) receiver
      have geometricSource := trajectory.movingReferenceGeometricObservables_eq_paper initialCircles (inside current member) source
      rw [← geometricReceiver.2.2, ← geometricSource.2.2] at estimate
      have timeBudget : ((15120 / Real.pi) * scales.strain + 1800 * tolerance) * current ≤ 1 / 4 :=
        (mul_le_mul_of_nonneg_left (member.2.trans terminalBound) pairNonnegative).trans (by nlinarith [pairBudget])
      have scaled := mul_le_mul_of_nonneg_right timeBudget gapPositive.le
      have finalEstimate := estimate.trans (by convert scaled using 1 <;> ring)
      dsimp only [referenceMechanicalMonitor]
      rw [if_neg same]
      linarith
  · intro current member label
    obtain ⟨⟨index, patch⟩, equality⟩ := finProdFinEquiv.surjective label
    subst label
    have estimate := absoluteEstimate current member index
    have timeBudget : (600 * tolerance + (3456 / Real.pi) * scales.strain +
        (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1)) * current ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (member.2.trans terminalBound) absoluteNonnegative).trans (by nlinarith [absoluteBudget])
    have centerBound := estimate.trans timeBudget
    have offset := (geometry current member index).centroidsBounded patch
    have triangle : ‖patchCentroid trajectory.movingFamily.patchMotion current index patch‖ ≤
        ‖patchCentroid trajectory.movingFamily.patchMotion current index patch - quadrupoleCenter trajectory.movingFamily.patchMotion current index‖ +
        ‖quadrupoleCenter trajectory.movingFamily.patchMotion current index - (scales.location (index.val + 1) : ℂ)‖ +
        ‖(scales.location (index.val + 1) : ℂ)‖ := by
      have identity : patchCentroid trajectory.movingFamily.patchMotion current index patch =
          (patchCentroid trajectory.movingFamily.patchMotion current index patch - quadrupoleCenter trajectory.movingFamily.patchMotion current index) +
          (quadrupoleCenter trajectory.movingFamily.patchMotion current index - (scales.location (index.val + 1) : ℂ)) +
          (scales.location (index.val + 1) : ℂ) := by abel
      calc
        _ = ‖(patchCentroid trajectory.movingFamily.patchMotion current index patch - quadrupoleCenter trajectory.movingFamily.patchMotion current index) +
            (quadrupoleCenter trajectory.movingFamily.patchMotion current index - (scales.location (index.val + 1) : ℂ)) +
            (scales.location (index.val + 1) : ℂ)‖ := congrArg norm identity
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scales.location_pos _)] at triangle
    have centerIdentity := trajectory.patchCentroid_eq_curve_center initialCircles (inside current member) index patch
    rw [centerIdentity] at triangle offset
    change ‖(trajectory.curve current).2.1 (finProdFinEquiv (index, patch))‖ - 3 < 0
    linarith [lengthSmall index, scales.location_le_one (index.val + 1)]

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
