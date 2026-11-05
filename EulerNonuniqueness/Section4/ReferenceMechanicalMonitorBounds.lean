import EulerNonuniqueness.Section4.ReferenceMechanicalMonitorSystem

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {scales : Scales} {shapeRadius gap margin shapeStop : ℝ} {state : MovingContourState (count * 4)}

theorem referenceMechanicalMonitor_clearance
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state .clearance ≤ 0) :
    margin ≤ infDist state (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := sub_nonpos.mp bound

theorem referenceMechanicalMonitor_strict_clearance
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state .clearance < 0) :
    margin < infDist state (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := sub_neg.mp bound

theorem referenceMechanicalMonitor_shape (label : Fin (count * 4))
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.shape label) ≤ 0) :
    ‖state.2.2 label - standardCircleBanach‖ ≤ shapeStop := sub_nonpos.mp bound

theorem referenceMechanicalMonitor_diagonal (index : Fin count)
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.diagonal index) ≤ 0) :
    scales.length (index.val + 1) ^ 2 / 2 ≤ movingReferenceDiagonalDifference state index ∧
      movingReferenceDiagonalDifference state index ≤ 2 * scales.length (index.val + 1) ^ 2 := by
  have estimate : |movingReferenceDiagonalDifference state index / scales.length (index.val + 1) ^ 2 - 1| ≤ 1 / 2 :=
    sub_nonpos.mp bound
  have denominatorPositive : 0 < scales.length (index.val + 1) ^ 2 := sq_pos_of_pos (scales.length_pos _)
  have lower := (abs_le.mp estimate).1
  have upper := (abs_le.mp estimate).2
  constructor
  · have quotient : (1 / 2 : ℝ) ≤ movingReferenceDiagonalDifference state index / scales.length (index.val + 1) ^ 2 := by linarith
    have multiplied := (le_div_iff₀ denominatorPositive).mp quotient
    linarith
  · have quotient : movingReferenceDiagonalDifference state index / scales.length (index.val + 1) ^ 2 ≤ 2 := by linarith
    exact (div_le_iff₀ denominatorPositive).mp quotient

theorem referenceMechanicalMonitor_asymmetry (index : Fin count)
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.asymmetry index) ≤ 0) :
    ‖movingReferenceAsymmetry state index‖ ≤ scales.length (index.val + 1) / 64 := by
  have estimate : ‖movingReferenceAsymmetry state index‖ / scales.length (index.val + 1) ≤ 1 / 64 := sub_nonpos.mp bound
  have multiplied := (div_le_iff₀ (scales.length_pos _)).mp estimate
  linarith

theorem referenceMechanicalMonitor_radial (index : Fin count)
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.radial index) ≤ 0) :
    |movingReferenceRadialObservable scales state index| ≤ 1 / 2 := sub_nonpos.mp bound

theorem referenceMechanicalMonitor_branch (index : Fin count)
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.branch index) ≤ 0) :
    1 / 16 ≤ movingReferenceRatioImaginary scales state index := sub_nonpos.mp bound

theorem referenceMechanicalMonitor_center (label : Fin (count * 4))
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.center label) ≤ 0) :
    ‖state.2.1 label‖ ≤ 3 := sub_nonpos.mp bound

theorem referenceMechanicalMonitor_pair (receiver source : Fin count) (different : receiver ≠ source)
    (bound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.pair receiver source) ≤ 0) :
    |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖movingReferenceCenter state receiver - movingReferenceCenter state source‖ ∧
      ‖movingReferenceCenter state receiver - movingReferenceCenter state source‖ ≤
        2 * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
  have estimate : ‖(movingReferenceCenter state receiver - movingReferenceCenter state source) -
      ((scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ))‖ ≤
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 := by
    apply sub_nonpos.mp
    simpa only [referenceMechanicalMonitor, if_neg different] using bound
  have locationNorm : ‖(scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ)‖ =
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have normEstimate := (abs_norm_sub_norm_le
    (movingReferenceCenter state receiver - movingReferenceCenter state source)
    ((scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ))).trans estimate
  rw [locationNorm] at normEstimate
  obtain ⟨lower, upper⟩ := abs_le.mp normEstimate
  constructor <;> linarith [abs_nonneg (scales.location (receiver.val + 1) - scales.location (source.val + 1))]

end EulerNonuniqueness.Paper
