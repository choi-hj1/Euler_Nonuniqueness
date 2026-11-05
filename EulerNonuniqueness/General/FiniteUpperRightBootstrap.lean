import EulerNonuniqueness.General.UpperRightBootstrap
import EulerNonuniqueness.General.ContinuousPrefixBootstrap
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Index Space : Type*} [Fintype Index]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem finite_curve_norm_bootstrap_of_upper_right_slopes
    {curve : Index → ℝ → Space} {terminal : ℝ} {radius rate : Index → ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (continuous : ∀ index, ContinuousOn (curve index) (Icc 0 terminal))
    (radiusPositive : ∀ index, 0 < radius index) (rateNonnegative : ∀ index, 0 ≤ rate index)
    (budget : ∀ index, ‖curve index 0‖ + rate index * terminal < radius index)
    (slopes : ∀ base ∈ Ico 0 terminal,
      (∀ current ∈ Icc 0 base, ∀ index, ‖curve index current‖ ≤ radius index) →
      ∀ index threshold, rate index < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖curve index current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal, ∀ index,
      ‖curve index time‖ ≤ ‖curve index 0‖ + rate index * time ∧
      ‖curve index time‖ < radius index := by
  let scaled : ℝ → Index → Space := fun time index => (radius index)⁻¹ • curve index time
  have scaledNorm (time : ℝ) (index : Index) :
      ‖scaled time index‖ = ‖curve index time‖ / radius index := by
    dsimp only [scaled]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (radiusPositive index)]
    ring
  have scaledContinuous : ContinuousOn scaled (Icc 0 terminal) := by
    apply continuousOn_pi.mpr
    intro index
    exact (continuous index).const_smul _
  have scaledInitial : ‖scaled 0‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro index
    rw [scaledNorm]
    apply (div_lt_iff₀ (radiusPositive index)).mpr
    have travel := mul_nonneg (rateNonnegative index) terminalNonnegative
    nlinarith [budget index]
  have recover (time : ℝ) (inside : ‖scaled time‖ ≤ 1) (index : Index) :
      ‖curve index time‖ ≤ radius index := by
    have component := (norm_le_pi_norm (scaled time) index).trans inside
    rw [scaledNorm] at component
    exact (div_le_iff₀ (radiusPositive index)).mp component |>.trans_eq (by ring)
  have scaledConfined := norm_strictly_confined_of_prefix_improvement scaledContinuous scaledInitial
    (by
      intro time inside prefixControl
      apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
      intro index
      have estimates := norm_le_linear_of_upper_right_slopes
        ((continuous index).mono (Icc_subset_Icc le_rfl inside.2))
        (by
          intro base baseInside threshold strict
          apply slopes base ⟨baseInside.1, baseInside.2.trans_le inside.2⟩
          · intro current currentInside other
            exact recover current (prefixControl current ⟨currentInside.1, currentInside.2.trans baseInside.2.le⟩) other
          · exact strict)
        time ⟨inside.1, le_rfl⟩
      have travel := mul_le_mul_of_nonneg_left inside.2 (rateNonnegative index)
      rw [scaledNorm]
      apply (div_lt_iff₀ (radiusPositive index)).mpr
      nlinarith [budget index])
  intro time inside index
  have estimate := norm_le_linear_of_upper_right_slopes (continuous index)
    (by
      intro base baseInside threshold strict
      apply slopes base baseInside
      · intro current currentInside other
        exact recover current (scaledConfined current ⟨currentInside.1, currentInside.2.trans baseInside.2.le⟩).le other
      · exact strict)
    time inside
  refine ⟨estimate, ?_⟩
  have travel := mul_le_mul_of_nonneg_left inside.2 (rateNonnegative index)
  linarith [budget index]

end EulerNonuniqueness.General
