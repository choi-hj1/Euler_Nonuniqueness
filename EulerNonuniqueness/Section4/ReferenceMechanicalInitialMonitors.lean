import EulerNonuniqueness.Section4.ReferenceMechanicalMonitorSystem
import EulerNonuniqueness.Section4.MovingReferenceMechanicalMonitorBounds
import EulerNonuniqueness.Section4.ReferenceInitialInvariants
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] mechanicalMonitorHolderSpace mechanicalMonitorC1Space

local instance initialMechanicalC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance initialMechanicalC1AddGroup : AddCommGroup PeriodicC1HolderHalf :=
  initialMechanicalC1Group.toAddCommGroup
local instance initialMechanicalC1Sub : Sub PeriodicC1HolderHalf := initialMechanicalC1AddGroup.toSub
local instance initialMechanicalC1Zero : Zero PeriodicC1HolderHalf := initialMechanicalC1AddGroup.toZero

def referenceMechanicalInitialState {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) : MovingContourState (count * 4) :=
  ((0 : ℝ), (fun label => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
    (phase (finProdFinEquiv.symm label).1) (unstable (finProdFinEquiv.symm label).1)
    (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach)

theorem initialDiskCenter_norm_le_two_of_length_small (scales : Scales) (index : ℕ)
    (phase unstable : ℝ) (small : |unstable| ≤ 1)
    (lengthSmall : scales.length index ≤ scales.location index / 1000) (patch : Fin 4) :
    ‖initialDiskCenter scales index phase unstable patch‖ ≤ 2 := by
  have bounds := initialDiagonals_norm_bound scales index phase unstable small
  have locationNorm : ‖(scales.location index : ℂ)‖ = scales.location index := by
    rw [Complex.norm_real, Real.norm_of_nonneg (scales.location_pos index).le]
  have diagonalBound :
      ‖if patch = 0 then initialPositiveDiagonal scales index phase unstable
        else if patch = 1 then -initialPositiveDiagonal scales index phase unstable
        else if patch = 2 then initialNegativeDiagonal scales index phase unstable
        else -initialNegativeDiagonal scales index phase unstable‖ ≤ 2 * scales.length index := by
    split_ifs <;> (try rw [norm_neg]) <;> linarith [bounds.1, bounds.2]
  have triangle := norm_add_le (scales.location index : ℂ)
    (if patch = 0 then initialPositiveDiagonal scales index phase unstable
      else if patch = 1 then -initialPositiveDiagonal scales index phase unstable
      else if patch = 2 then initialNegativeDiagonal scales index phase unstable
      else -initialNegativeDiagonal scales index phase unstable)
  rw [locationNorm] at triangle
  change ‖(scales.location index : ℂ) + _‖ ≤ 2
  linarith [scales.location_le_one index]

theorem referenceMechanicalInitialState_geometric_values {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) (small : ∀ index, |unstable index| ≤ 1 / 2) (index : Fin count) :
    movingReferenceDiagonalDifference (referenceMechanicalInitialState scales phase unstable) index =
      scales.length (index.val + 1) ^ 2 ∧
    movingReferenceAsymmetry (referenceMechanicalInitialState scales phase unstable) index = 0 ∧
    movingReferenceCenter (referenceMechanicalInitialState scales phase unstable) index =
      (scales.location (index.val + 1) : ℂ) := by
  have positive : movingReferencePositiveDiagonal (referenceMechanicalInitialState scales phase unstable) index =
      initialPositiveDiagonal scales (index.val + 1) (phase index) (unstable index) := by
    simp only [movingReferencePositiveDiagonal, referenceMechanicalInitialState, Equiv.symm_apply_apply,
      initialDiskCenter, Fin.reduceEq, if_true, if_false]
    ring
  have negative : movingReferenceNegativeDiagonal (referenceMechanicalInitialState scales phase unstable) index =
      initialNegativeDiagonal scales (index.val + 1) (phase index) (unstable index) := by
    simp only [movingReferenceNegativeDiagonal, referenceMechanicalInitialState, Equiv.symm_apply_apply,
      initialDiskCenter, Fin.reduceEq, if_true, if_false]
    ring
  constructor
  · rw [movingReferenceDiagonalDifference, positive, negative]
    exact initialDiagonals_diagonalDifference scales _ _ _ (small index)
  constructor
  · simp only [movingReferenceAsymmetry, referenceMechanicalInitialState, Equiv.symm_apply_apply,
      initialDiskCenter, Fin.reduceEq, if_true, if_false]
    ring
  · simp only [movingReferenceCenter, referenceMechanicalInitialState, Fin.sum_univ_four, Equiv.symm_apply_apply,
      initialDiskCenter, Fin.reduceEq, if_true, if_false]
    ring

theorem referenceMechanicalMonitor_initial_strict {count : ℕ}
    (configuration : FiniteContourConfiguration (count * 4)) (scales : Scales)
    (phase unstable : Fin count → ℝ) {shapeRadius gap margin shapeStop radius : ℝ}
    (marginPositive : 0 < margin) (shapeStopPositive : 0 < shapeStop) (radiusSmall : radius ≤ 1 / 8)
    (small : ∀ index, |unstable index| ≤ radius)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (initialMargin : 2 * margin ≤ infDist (referenceMechanicalInitialState scales phase unstable)
      (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ) :
    ∀ monitor, referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop
      (referenceMechanicalInitialState scales phase unstable) monitor < 0 := by
  have halfSmall : ∀ index, |unstable index| ≤ 1 / 2 := fun index => (small index).trans (by linarith)
  have unitSmall : ∀ index, |unstable index| ≤ 1 := fun index => (small index).trans (by linarith)
  intro monitor
  cases monitor with
  | clearance => change margin - _ < 0; linarith
  | shape label =>
      change ‖standardCircleBanach - standardCircleBanach‖ - shapeStop < 0
      with_reducible_and_instances
        simpa only [sub_self, norm_zero, zero_sub] using neg_neg_of_pos shapeStopPositive
  | diagonal index =>
      have values := referenceMechanicalInitialState_geometric_values scales phase unstable halfSmall index
      change |movingReferenceDiagonalDifference _ index / scales.length (index.val + 1) ^ 2 - 1| - 1 / 2 < 0
      rw [values.1, div_self (ne_of_gt (sq_pos_of_pos (scales.length_pos _)))]
      norm_num
  | asymmetry index =>
      have values := referenceMechanicalInitialState_geometric_values scales phase unstable halfSmall index
      change ‖movingReferenceAsymmetry _ index‖ / scales.length (index.val + 1) - 1 / 64 < 0
      rw [values.2.1, norm_zero, zero_div]
      norm_num
  | radial index =>
      exact (movingReferenceMechanicalMonitors_initial_strict scales phase unstable radiusSmall small index).1
  | branch index =>
      exact (movingReferenceMechanicalMonitors_initial_strict scales phase unstable radiusSmall small index).2
  | pair receiver source =>
      by_cases same : receiver = source
      · simp only [referenceMechanicalMonitor, same, if_true]
        norm_num
      · have receiverValues := referenceMechanicalInitialState_geometric_values scales phase unstable halfSmall receiver
        have sourceValues := referenceMechanicalInitialState_geometric_values scales phase unstable halfSmall source
        have indicesDifferent : receiver.val + 1 ≠ source.val + 1 :=
          fun equality => same (Fin.ext (Nat.add_right_cancel equality))
        simp only [referenceMechanicalMonitor, if_neg same, receiverValues.2.2, sourceValues.2.2, sub_self, norm_zero]
        linarith [scales.location_distance_pos indicesDifferent]
  | center label =>
      have bound := initialDiskCenter_norm_le_two_of_length_small scales ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable (finProdFinEquiv.symm label).1)
        (unitSmall _) (lengthSmall _) (finProdFinEquiv.symm label).2
      change ‖initialDiskCenter scales _ _ _ _‖ - 3 < 0
      linarith

end EulerNonuniqueness.Paper
