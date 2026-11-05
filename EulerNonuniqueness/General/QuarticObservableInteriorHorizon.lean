import EulerNonuniqueness.General.FiniteObservableInteriorSlope
import EulerNonuniqueness.General.QuarticMaterialBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem exists_uniform_quartic_observable_bootstrap_root_with_interior_slopes_on_horizon
    {forcingConstant initialConstant normalConstant recoveryCoefficient recoveryLoss horizon : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (initialNonnegative : 0 ≤ initialConstant)
    (normalNonnegative : 0 ≤ normalConstant) (recoveryNonnegative : 0 ≤ recoveryCoefficient)
    (lossNonnegative : 0 ≤ recoveryLoss) (horizonNonnegative : 0 ≤ horizon) :
    ∃ rootMin ≥ (8 : ℝ), ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
      ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ horizon →
      ∀ {Index : Type*} [Fintype Index] (frequency weight geometricRatio numerator : Index → ℝ),
      (∀ index, 1 ≤ frequency index) → (∀ index, 0 ≤ weight index) →
      (∀ index, weight index ≤ forcingConstant * frequency index) →
      (∀ index, 0 ≤ geometricRatio index) →
      (∀ index, geometricRatio index ≤ forcingConstant / (scaleRoot * frequency index)) →
      (∀ index, 0 ≤ numerator index) → (∀ index, numerator index ≤ forcingConstant * frequency index ^ 2) →
      let strength := fun index => scaleRoot ^ 3 * frequency index ^ 4
      let radius := fun index => (forcingConstant + 1) / (scaleRoot ^ 2 * frequency index ^ 2)
      let rate := fun index => normalConstant *
        (strength index * radius index ^ 3 + weight index * radius index ^ 2 +
          weight index * geometricRatio index * radius index + numerator index / strength index)
      ∀ (controlled : Index → ℝ → Space) (observable : Index → ℝ → Target),
      (∀ index, ContinuousOn (controlled index) (Icc 0 terminal)) →
      (∀ index, ContinuousOn (observable index) (Icc 0 terminal)) →
      (∀ index, ‖observable index 0‖ ≤ initialConstant * (weight index / strength index)) →
      (∀ time ∈ Icc 0 terminal, ∀ index, ‖controlled index time‖ ≤
        recoveryCoefficient * ‖observable index time‖ + recoveryLoss * (weight index / strength index)) →
      (∀ base ∈ Ioo 0 terminal,
        (∀ current ∈ Icc 0 base, ∀ index, ‖controlled index current‖ ≤ radius index) →
        ∀ index threshold, rate index < threshold →
          ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖observable index current‖) base later < threshold) →
      ∀ time ∈ Icc 0 terminal, ∀ index,
        ‖observable index time‖ ≤ ‖observable index 0‖ + rate index * time ∧
        ‖controlled index time‖ < radius index / 8 := by
  obtain ⟨rootMin, rootEight, scalarBudget⟩ := exists_uniform_quartic_material_budget_root
    forcingNonnegative
    (show 0 ≤ recoveryCoefficient * initialConstant + recoveryLoss by positivity)
    (show 0 ≤ recoveryCoefficient * normalConstant by positivity) horizonNonnegative
  refine ⟨rootMin, rootEight, ?_⟩
  intro scaleRoot rootLarge terminal terminalNonnegative terminalBound Index indexFinite frequency weight geometricRatio numerator
    frequencyLarge weightNonnegative weightBound ratioNonnegative ratioBound numeratorNonnegative numeratorBound
  let strength := fun index => scaleRoot ^ 3 * frequency index ^ 4
  let radius := fun index => (forcingConstant + 1) / (scaleRoot ^ 2 * frequency index ^ 2)
  let rate := fun index => normalConstant *
    (strength index * radius index ^ 3 + weight index * radius index ^ 2 +
      weight index * geometricRatio index * radius index + numerator index / strength index)
  dsimp only
  intro controlled observable controlledContinuous observableContinuous initialBound recovery slopes
  have rootPositive : 0 < scaleRoot := by linarith [rootEight.trans rootLarge]
  have radiusPositive (index : Index) : 0 < radius index := by
    have omegaPositive : 0 < frequency index := by linarith [frequencyLarge index]
    dsimp only [radius]
    positivity
  have rateNonnegative (index : Index) : 0 ≤ rate index := by
    have omegaPositive : 0 < frequency index := by linarith [frequencyLarge index]
    have weightPositive := weightNonnegative index
    have ratioPositive := ratioNonnegative index
    have numeratorPositive := numeratorNonnegative index
    dsimp only [rate, radius, strength]
    positivity
  have horizonBudget (index : Index) :
      recoveryCoefficient * (‖observable index 0‖ + rate index * horizon) +
        recoveryLoss * (weight index / strength index) < radius index / 8 := by
    have scalar := scalarBudget scaleRoot rootLarge (frequency index) (frequencyLarge index)
      (weight index) (geometricRatio index) (numerator index)
      (weightBound index) (ratioNonnegative index) (ratioBound index) (numeratorBound index)
    have estimate : recoveryCoefficient * (‖observable index 0‖ + rate index * horizon) +
        recoveryLoss * (weight index / strength index) ≤
      (recoveryCoefficient * initialConstant + recoveryLoss) * (weight index / strength index) +
        (recoveryCoefficient * normalConstant) * horizon *
          (strength index * radius index ^ 3 + weight index * radius index ^ 2 +
            weight index * geometricRatio index * radius index + numerator index / strength index) := by
      calc
        _ ≤ recoveryCoefficient *
            (initialConstant * (weight index / strength index) + rate index * horizon) +
              recoveryLoss * (weight index / strength index) :=
          add_le_add_right (mul_le_mul_of_nonneg_left
            (add_le_add_right (initialBound index) (rate index * horizon)) recoveryNonnegative) _
        _ = _ := by dsimp only [rate]; ring
    exact estimate.trans_lt scalar
  have strictBudget (index : Index) :
      recoveryCoefficient * (‖observable index 0‖ + rate index * terminal) +
        recoveryLoss * (weight index / strength index) < radius index / 8 := by
    have enlarged := mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left terminalBound (rateNonnegative index))
        ‖observable index 0‖) recoveryNonnegative
    exact (add_le_add_right enlarged (recoveryLoss * (weight index / strength index))).trans_lt (horizonBudget index)
  have estimates := finite_observable_bootstrap_of_upper_right_interior_slopes terminalNonnegative
    controlledContinuous observableContinuous radiusPositive rateNonnegative
    (fun _ => recoveryNonnegative)
    (by
      intro index
      have strict := strictBudget index
      linarith [radiusPositive index])
    recovery slopes
  intro time inside index
  have observed := (estimates time inside index).1
  refine ⟨observed, ?_⟩
  have travel := mul_le_mul_of_nonneg_left inside.2 (rateNonnegative index)
  have terminalBound : ‖observable index time‖ ≤ ‖observable index 0‖ + rate index * terminal := by linarith
  have multiplied := mul_le_mul_of_nonneg_left terminalBound recoveryNonnegative
  linarith [recovery time inside index, strictBudget index]

end EulerNonuniqueness.General
