import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.General

theorem exponentialResponse_comp_eq_div_sub
    {forcing : ℝ → ℝ} {growth decay : ℝ} (regular : Continuous forcing)
    (different : growth ≠ decay) (time : ℝ) :
    exponentialResponse decay (exponentialResponse growth forcing) time =
      (exponentialResponse growth forcing time - exponentialResponse decay forcing time) / (growth - decay) := by
  let candidate := fun current =>
    (exponentialResponse growth forcing current - exponentialResponse decay forcing current) / (growth - decay)
  have innerContinuous : Continuous (exponentialResponse growth forcing) :=
    continuous_iff_continuousAt.mpr fun current => (hasDerivAt_exponentialResponse regular growth current).continuousAt
  have candidateDerivative (current : ℝ) :
      HasDerivAt candidate (decay * candidate current + exponentialResponse growth forcing current) current := by
    convert ((hasDerivAt_exponentialResponse regular growth current).sub
      (hasDerivAt_exponentialResponse regular decay current)).div_const (growth - decay) using 1
    dsimp only [candidate]
    field_simp [sub_ne_zero.mpr different]
    <;> ring
  let difference := fun current => Real.exp (-decay * current) *
    (exponentialResponse decay (exponentialResponse growth forcing) current - candidate current)
  have derivative (current : ℝ) : HasDerivAt difference 0 current := by
    convert ((((hasDerivAt_id current).const_mul (-decay)).exp).mul
      ((hasDerivAt_exponentialResponse innerContinuous decay current).sub (candidateDerivative current))) using 1
    dsimp only [id_eq]
    ring
  have equality := is_const_of_deriv_eq_zero (fun current => (derivative current).differentiableAt)
    (fun current => (derivative current).deriv) time 0
  have initial : difference 0 = 0 := by simp [difference, candidate, exponentialResponse]
  rw [initial] at equality
  change Real.exp (-decay * time) *
    (exponentialResponse decay (exponentialResponse growth forcing) time - candidate time) = 0 at equality
  exact sub_eq_zero.mp ((mul_eq_zero.mp equality).resolve_left (Real.exp_pos _).ne')

theorem iterated_exponential_convolution_le_on_Icc
    {forcing : ℝ → ℝ} {growth decay horizon : ℝ}
    (regular : ContinuousOn forcing (Icc 0 horizon)) (horizonNonnegative : 0 ≤ horizon)
    (gap : decay < growth) (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time) :
    ∀ time ∈ Icc 0 horizon,
      (∫ current in (0 : ℝ)..time, Real.exp (decay * (time - current)) *
        (∫ earlier in (0 : ℝ)..current, Real.exp (growth * (current - earlier)) * forcing earlier)) ≤
      (∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) * forcing current) / (growth - decay) := by
  let extended := fun time => forcing (projIcc 0 horizon horizonNonnegative time)
  have extendedContinuous : Continuous extended :=
    continuousOn_iff_continuous_restrict.mp regular |>.comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 horizon) : extended time = forcing time := by
    simp only [extended, projIcc_of_mem horizonNonnegative inside]
  have responseAgreement (rate time : ℝ) (inside : time ∈ Icc 0 horizon) :
      exponentialResponse rate extended time =
        ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current := by
    rw [exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current currentInside
    rw [uIcc_of_le inside.1] at currentInside
    change Real.exp (rate * (time - current)) * extended current = _
    rw [agreement current ⟨currentInside.1, currentInside.2.trans inside.2⟩]
  intro time inside
  have slowNonnegative : 0 ≤ exponentialResponse decay extended time :=
    exponentialResponse_nonnegative inside.1 (fun current member => by
      rw [agreement current ⟨member.1, member.2.trans inside.2⟩]
      exact nonnegative current ⟨member.1, member.2.trans inside.2⟩)
  have comparison : exponentialResponse decay (exponentialResponse growth extended) time ≤
      exponentialResponse growth extended time / (growth - decay) := by
    rw [exponentialResponse_comp_eq_div_sub extendedContinuous (ne_of_gt gap)]
    exact div_le_div_of_nonneg_right (sub_le_self _ slowNonnegative) (sub_pos.mpr gap).le
  have nestedAgreement : exponentialResponse decay (exponentialResponse growth extended) time =
      ∫ current in (0 : ℝ)..time, Real.exp (decay * (time - current)) *
        (∫ earlier in (0 : ℝ)..current, Real.exp (growth * (current - earlier)) * forcing earlier) := by
    rw [exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current currentInside
    rw [uIcc_of_le inside.1] at currentInside
    change Real.exp (decay * (time - current)) * exponentialResponse growth extended current = _
    rw [responseAgreement growth current ⟨currentInside.1, currentInside.2.trans inside.2⟩]
  rw [nestedAgreement, responseAgreement growth time inside] at comparison
  exact comparison

end EulerNonuniqueness.General
