import EulerNonuniqueness.Section6.ForcedDipoleBootstrap

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_forced_continued_separation
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {residual : ℝ → FourPointConfiguration} {region : ℝ → Set ℂ}
    {frequency length initialDistance horizon error : ℝ} {strain : ℝ≥0} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon) (errorNonnegative : 0 ≤ error)
    (relativeSmall : 64 * ((strain : ℝ) + error) * horizon ≤ 1)
    (centerSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2) (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target +
        external time (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual time target) time)
    (externalLipschitz : ∀ time ∈ Icc 0 horizon, LipschitzOnWith strain (external time) (region time))
    (inside : ∀ time ∈ Icc 0 horizon, ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region time)
    (residualBound : ∀ time ∈ Icc 0 horizon, ‖residual time‖ ≤ error * length)
    (firstInitial : ‖firstSeparation 0 - (length : ℂ) * direction‖ ≤ length / 64)
    (secondInitial : ‖secondSeparation 0 - (length : ℂ) * (-direction)‖ ≤ length / 64)
    (initialProjection : (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤ (5 / 4 : ℝ) * length * initialDistance) :
    ∀ time ∈ Icc 0 horizon,
      ‖firstSeparation time - (length : ℂ) * direction‖ ≤ length / 16 ∧
      ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤ length / 16 ∧
      (3 / 4 : ℝ) * length * (initialDistance + frequency * time) ≤ ‖firstCenter time - secondCenter time‖ ∧
      ‖firstCenter time - secondCenter time‖ ≤ 3 * length * (initialDistance + frequency * time) := by
  let monitor := fun time => max (‖firstSeparation time‖ - 2 * length)
    (max (‖secondSeparation time‖ - 2 * length)
      (max (length * (initialDistance + frequency * time) / 4 - ‖firstCenter time - secondCenter time‖)
        (‖firstCenter time - secondCenter time‖ - 4 * length * (initialDistance + frequency * time))))
  have firstContinuous : ContinuousOn firstSeparation (Icc 0 horizon) := by
    intro time member
    exact (twoDipole_first_pair_forced_equations (equation time member)).2.continuousAt.continuousWithinAt
  have secondContinuous : ContinuousOn secondSeparation (Icc 0 horizon) := by
    intro time member
    have continuous := ((equation time member 1).sub (equation time member 3)).continuousAt
    have identity : (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) 1 -
      twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) 3) = secondSeparation := by
      funext current
      simp [twoDipoleConfiguration]
    rw [identity] at continuous
    exact continuous.continuousWithinAt
  have centerContinuous : ContinuousOn (fun time => firstCenter time - secondCenter time) (Icc 0 horizon) :=
    fun time member => (twoDipole_centers_actual_forced_equation (equation time member)).continuousAt.continuousWithinAt
  have lowerAffineContinuous : ContinuousOn (fun time => length * (initialDistance + frequency * time) / 4) (Icc 0 horizon) := by
    fun_prop
  have upperAffineContinuous : ContinuousOn (fun time => 4 * length * (initialDistance + frequency * time)) (Icc 0 horizon) := by
    fun_prop
  have monitorContinuous : ContinuousOn monitor (Icc 0 horizon) := by
    have combine {first second : ℝ → ℝ} (firstContinuous : ContinuousOn first (Icc 0 horizon))
        (secondContinuous : ContinuousOn second (Icc 0 horizon)) :
        ContinuousOn (fun time => max (first time) (second time)) (Icc 0 horizon) :=
      continuous_max.comp_continuousOn (firstContinuous.prodMk secondContinuous)
    exact combine (firstContinuous.norm.sub continuousOn_const)
      (combine (secondContinuous.norm.sub continuousOn_const)
        (combine (lowerAffineContinuous.sub centerContinuous.norm) (centerContinuous.norm.sub upperAffineContinuous)))
  have firstIdealNorm : ‖(length : ℂ) * direction‖ = length := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, directionNorm, mul_one]
  have secondIdealNorm : ‖(length : ℂ) * (-direction)‖ = length := by
    simpa only [mul_neg, norm_neg] using firstIdealNorm
  have initialProjectionBound : (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re ≤
      ‖firstCenter 0 - secondCenter 0‖ := by
    apply (Complex.re_le_norm _).trans
    simp only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul, le_refl]
  have monitorInitial : monitor 0 < 0 := by
    have firstTriangle := norm_add_le (firstSeparation 0 - (length : ℂ) * direction) ((length : ℂ) * direction)
    rw [sub_add_cancel, firstIdealNorm] at firstTriangle
    have secondTriangle := norm_add_le (secondSeparation 0 - (length : ℂ) * (-direction)) ((length : ℂ) * (-direction))
    rw [sub_add_cancel, secondIdealNorm] at secondTriangle
    dsimp only [monitor]
    simp only [max_lt_iff, mul_zero, add_zero]
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> nlinarith
  have improvement : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, monitor current ≤ 0) → monitor time < 0 := by
    intro time member prior
    have priorBounds (current : ℝ) (currentInside : current ∈ Icc 0 time) :
        ‖firstSeparation current‖ ≤ 2 * length ∧ ‖secondSeparation current‖ ≤ 2 * length ∧
          length * (initialDistance + frequency * current) / 4 ≤ ‖firstCenter current - secondCenter current‖ ∧
          ‖firstCenter current - secondCenter current‖ ≤ 4 * length * (initialDistance + frequency * current) := by
      simpa only [monitor, max_le_iff, sub_nonpos] using prior current currentInside
    have relativeSmallTime : 64 * ((strain : ℝ) + error) * time ≤ 1 :=
      (mul_le_mul_of_nonneg_left member.2 (by positivity : 0 ≤ 64 * ((strain : ℝ) + error))).trans relativeSmall
    have centerSmallTime : 8 * (strain : ℝ) * (time + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left member.2 strain.coe_nonneg]
    have upgraded := twoDipole_forced_bootstrap_improvement frequencyPositive lengthPositive directionNorm initialDistanceLarge member.1
      errorNonnegative relativeSmallTime centerSmallTime
      (fun current currentInside => equation current ⟨currentInside.1, currentInside.2.trans member.2⟩)
      (fun current currentInside => externalLipschitz current ⟨currentInside.1, currentInside.2.trans member.2⟩)
      (fun current currentInside => inside current ⟨currentInside.1, currentInside.2.trans member.2⟩)
      (fun current currentInside => residualBound current ⟨currentInside.1, currentInside.2.trans member.2⟩)
      firstInitial secondInitial initialProjection initialUpper
      (fun current currentInside => (priorBounds current currentInside).1)
      (fun current currentInside => (priorBounds current currentInside).2.1)
      (fun current currentInside => (priorBounds current currentInside).2.2.1)
      (fun current currentInside => (priorBounds current currentInside).2.2.2)
      time ⟨member.1, le_rfl⟩
    have firstTriangle := norm_add_le (firstSeparation time - (length : ℂ) * direction) ((length : ℂ) * direction)
    rw [sub_add_cancel, firstIdealNorm] at firstTriangle
    have secondTriangle := norm_add_le (secondSeparation time - (length : ℂ) * (-direction)) ((length : ℂ) * (-direction))
    rw [sub_add_cancel, secondIdealNorm] at secondTriangle
    have positiveTime : 0 ≤ frequency * time := mul_nonneg frequencyPositive.le member.1
    dsimp only [monitor]
    simp only [max_lt_iff]
    refine ⟨by linarith [upgraded.1], by linarith [upgraded.2.1], ?_, ?_⟩ <;>
      nlinarith [upgraded.2.2.1, upgraded.2.2.2]
  have strict := strict_bootstrap_on_Icc monitorContinuous monitorInitial improvement
  have bootstrap (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖firstSeparation time‖ ≤ 2 * length ∧ ‖secondSeparation time‖ ≤ 2 * length ∧
        length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖ ∧
        ‖firstCenter time - secondCenter time‖ ≤ 4 * length * (initialDistance + frequency * time) := by
    simpa only [monitor, max_le_iff, sub_nonpos] using (strict time member).le
  exact twoDipole_forced_bootstrap_improvement frequencyPositive lengthPositive directionNorm initialDistanceLarge horizonNonnegative
    errorNonnegative relativeSmall centerSmall equation externalLipschitz inside residualBound
    firstInitial secondInitial initialProjection initialUpper
    (fun time member => (bootstrap time member).1)
    (fun time member => (bootstrap time member).2.1)
    (fun time member => (bootstrap time member).2.2.1)
    (fun time member => (bootstrap time member).2.2.2)

end EulerNonuniqueness.Section6
