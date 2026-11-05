import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Int

noncomputable section

open Set

namespace EulerNonuniqueness.General

theorem phase_continuous_lift_unique_on_Icc {first second : ℝ → ℝ} {horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (firstContinuous : ContinuousOn first (Icc 0 horizon))
    (secondContinuous : ContinuousOn second (Icc 0 horizon))
    (initial : first 0 = second 0)
    (sameExponential : ∀ time ∈ Icc 0 horizon,
      Complex.exp (Complex.I * (first time : ℂ)) = Complex.exp (Complex.I * (second time : ℂ))) :
    EqOn first second (Icc 0 horizon) := by
  let periods := fun time => (first time - second time) / (2 * Real.pi)
  have periodsContinuous : ContinuousOn periods (Icc 0 horizon) :=
    (firstContinuous.sub secondContinuous).div_const _
  have periodsInteger : MapsTo periods (Icc 0 horizon) (range ((↑) : ℤ → ℝ)) := by
    intro time inside
    obtain ⟨integer, periodic⟩ := Complex.exp_eq_exp_iff_exists_int.mp (sameExponential time inside)
    have imaginary := congrArg Complex.im periodic
    simp [Complex.mul_im] at imaginary
    refine ⟨integer, ?_⟩
    dsimp only [periods]
    apply Eq.symm
    apply (div_eq_iff (ne_of_gt Real.two_pi_pos)).mpr
    linarith only [imaginary]
  letI : DiscreteTopology (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isEmbedding.toHomeomorph.symm.isEmbedding.discreteTopology
  intro time inside
  have constant := isPreconnected_Icc.constant_of_mapsTo periodsContinuous periodsInteger inside
    (show (0 : ℝ) ∈ Icc 0 horizon from ⟨le_rfl, horizonNonnegative⟩)
  dsimp only [periods] at constant
  rw [initial, sub_self, zero_div] at constant
  have difference := (div_eq_iff (ne_of_gt Real.two_pi_pos)).mp constant
  exact sub_eq_zero.mp (by simpa only [zero_mul] using difference)

theorem phase_polar_lift_unique_on_Icc {path : ℝ → ℂ} {first second : ℝ → ℝ} {horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (firstContinuous : ContinuousOn first (Icc 0 horizon))
    (secondContinuous : ContinuousOn second (Icc 0 horizon))
    (initial : first 0 = second 0)
    (nonzero : ∀ time ∈ Icc 0 horizon, path time ≠ 0)
    (firstPolar : ∀ time ∈ Icc 0 horizon,
      path time = (‖path time‖ : ℂ) * Complex.exp (Complex.I * (first time : ℂ)))
    (secondPolar : ∀ time ∈ Icc 0 horizon,
      path time = (‖path time‖ : ℂ) * Complex.exp (Complex.I * (second time : ℂ))) :
    EqOn first second (Icc 0 horizon) := by
  apply phase_continuous_lift_unique_on_Icc horizonNonnegative firstContinuous secondContinuous initial
  intro time inside
  have normNonzero : (‖path time‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (nonzero time inside))
  exact mul_left_cancel₀ normNonzero ((firstPolar time inside).symm.trans (secondPolar time inside))

end EulerNonuniqueness.General
