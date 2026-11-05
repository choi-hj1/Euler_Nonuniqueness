import EulerNonuniqueness.General.FiniteUpperRightBootstrap
import EulerNonuniqueness.General.InteriorUpperRightNormGrowth

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Index Space Target : Type*} [Fintype Index]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem finite_observable_bootstrap_of_upper_right_interior_slopes
    {controlled : Index → ℝ → Space} {observable : Index → ℝ → Target}
    {terminal : ℝ} {radius rate coefficient loss : Index → ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (controlledContinuous : ∀ index, ContinuousOn (controlled index) (Icc 0 terminal))
    (observableContinuous : ∀ index, ContinuousOn (observable index) (Icc 0 terminal))
    (radiusPositive : ∀ index, 0 < radius index) (rateNonnegative : ∀ index, 0 ≤ rate index)
    (coefficientNonnegative : ∀ index, 0 ≤ coefficient index)
    (budget : ∀ index, coefficient index * (‖observable index 0‖ + rate index * terminal) + loss index < radius index)
    (recovery : ∀ time ∈ Icc 0 terminal, ∀ index,
      ‖controlled index time‖ ≤ coefficient index * ‖observable index time‖ + loss index)
    (slopes : ∀ base ∈ Ioo 0 terminal,
      (∀ current ∈ Icc 0 base, ∀ index, ‖controlled index current‖ ≤ radius index) →
      ∀ index threshold, rate index < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖observable index current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal, ∀ index,
      ‖observable index time‖ ≤ ‖observable index 0‖ + rate index * time ∧
      ‖controlled index time‖ < radius index := by
  let scaled : ℝ → Index → Space := fun time index => (radius index)⁻¹ • controlled index time
  have scaledNorm (time : ℝ) (index : Index) :
      ‖scaled time index‖ = ‖controlled index time‖ / radius index := by
    dsimp only [scaled]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (radiusPositive index)]
    ring
  have scaledContinuous : ContinuousOn scaled (Icc 0 terminal) := by
    apply continuousOn_pi.mpr
    intro index
    exact (controlledContinuous index).const_smul _
  have initialBound (index : Index) : ‖controlled index 0‖ < radius index := by
    have initialRecovery := recovery 0 ⟨le_rfl, terminalNonnegative⟩ index
    have travel := mul_nonneg (rateNonnegative index) terminalNonnegative
    have multiplied := mul_le_mul_of_nonneg_left (show ‖observable index 0‖ ≤
      ‖observable index 0‖ + rate index * terminal by linarith) (coefficientNonnegative index)
    linarith [budget index]
  have scaledInitial : ‖scaled 0‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro index
    rw [scaledNorm]
    exact (div_lt_iff₀ (radiusPositive index)).mpr (by simpa only [one_mul] using initialBound index)
  have recoverRadius (time : ℝ) (inside : ‖scaled time‖ ≤ 1) (index : Index) :
      ‖controlled index time‖ ≤ radius index := by
    have component := (norm_le_pi_norm (scaled time) index).trans inside
    rw [scaledNorm] at component
    exact (div_le_iff₀ (radiusPositive index)).mp component |>.trans_eq (by ring)
  have scaledConfined := norm_strictly_confined_of_prefix_improvement scaledContinuous scaledInitial
    (by
      intro time inside prefixControl
      apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
      intro index
      have estimate := norm_le_linear_of_upper_right_interior_slopes
        ((observableContinuous index).mono (Icc_subset_Icc le_rfl inside.2))
        (by
          intro base baseInside threshold strict
          apply slopes base ⟨baseInside.1, baseInside.2.trans_le inside.2⟩
          · intro current currentInside other
            exact recoverRadius current (prefixControl current
              ⟨currentInside.1, currentInside.2.trans baseInside.2.le⟩) other
          · exact strict)
        time ⟨inside.1, le_rfl⟩
      have travel := mul_le_mul_of_nonneg_left inside.2 (rateNonnegative index)
      have observableBound : ‖observable index time‖ ≤ ‖observable index 0‖ + rate index * terminal := by
        linarith
      have multiplied := mul_le_mul_of_nonneg_left observableBound (coefficientNonnegative index)
      have controlledStrict : ‖controlled index time‖ < radius index := by
        linarith [recovery time inside index, budget index]
      rw [scaledNorm]
      exact (div_lt_iff₀ (radiusPositive index)).mpr (by simpa only [one_mul] using controlledStrict))
  intro time inside index
  have estimate := norm_le_linear_of_upper_right_interior_slopes (observableContinuous index)
    (by
      intro base baseInside threshold strict
      apply slopes base baseInside
      · intro current currentInside other
        exact recoverRadius current (scaledConfined current
          ⟨currentInside.1, currentInside.2.trans baseInside.2.le⟩).le other
      · exact strict)
    time inside
  refine ⟨estimate, ?_⟩
  have component := (norm_le_pi_norm (scaled time) index).trans_lt (scaledConfined time inside)
  rw [scaledNorm] at component
  exact (div_lt_iff₀ (radiusPositive index)).mp component |>.trans_eq (by ring)

end EulerNonuniqueness.General
