import EulerNonuniqueness.Section6.StoppedBootstrap

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem twoDipole_continued_separation
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {frequency length initialDistance horizon : ℝ} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target) time)
    (firstInitial : ‖firstSeparation 0 - (length : ℂ) * direction‖ ≤ length / 32)
    (secondInitial : ‖secondSeparation 0 - (length : ℂ) * (-direction)‖ ≤ length / 32)
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
      (length * (initialDistance + frequency * time) / 4 - ‖firstCenter time - secondCenter time‖))
  have firstContinuous : ContinuousOn firstSeparation (Icc 0 horizon) := by
    intro time member
    exact (twoDipole_first_pair_equations (equation time member)).2.continuousAt.continuousWithinAt
  have secondContinuous : ContinuousOn secondSeparation (Icc 0 horizon) := by
    intro time member
    have continuous := ((equation time member 1).sub (equation time member 3)).continuousAt
    have identity : (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) 1 -
      twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) 3) = secondSeparation := by
      funext current
      simp [twoDipoleConfiguration] <;> ring
    rw [identity] at continuous
    exact continuous.continuousWithinAt
  have centerContinuous : ContinuousOn (fun time => firstCenter time - secondCenter time) (Icc 0 horizon) :=
    fun time member => (twoDipole_centers_actual_equation (equation time member)).continuousAt.continuousWithinAt
  have affineContinuous : ContinuousOn (fun time => length * (initialDistance + frequency * time) / 4) (Icc 0 horizon) := by
    fun_prop
  have monitorContinuous : ContinuousOn monitor (Icc 0 horizon) := by
    have combine {first second : ℝ → ℝ} (firstContinuous : ContinuousOn first (Icc 0 horizon))
        (secondContinuous : ContinuousOn second (Icc 0 horizon)) :
        ContinuousOn (fun time => max (first time) (second time)) (Icc 0 horizon) :=
      continuous_max.comp_continuousOn (firstContinuous.prodMk secondContinuous)
    exact combine (firstContinuous.norm.sub continuousOn_const)
      (combine (secondContinuous.norm.sub continuousOn_const) (affineContinuous.sub centerContinuous.norm))
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
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith
  have improvement : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, monitor current ≤ 0) → monitor time < 0 := by
    intro time member prior
    have priorBounds (current : ℝ) (currentInside : current ∈ Icc 0 time) :
        ‖firstSeparation current‖ ≤ 2 * length ∧ ‖secondSeparation current‖ ≤ 2 * length ∧
          length * (initialDistance + frequency * current) / 4 ≤ ‖firstCenter current - secondCenter current‖ := by
      simpa only [monitor, max_le_iff, sub_nonpos] using prior current currentInside
    have upgraded := twoDipole_bootstrap_improvement frequencyPositive lengthPositive directionNorm initialDistanceLarge member.1
      (fun current currentInside => equation current ⟨currentInside.1, currentInside.2.trans member.2⟩)
      firstInitial secondInitial initialProjection initialUpper
      (fun current currentInside => (priorBounds current currentInside).1)
      (fun current currentInside => (priorBounds current currentInside).2.1)
      (fun current currentInside => (priorBounds current currentInside).2.2)
      time ⟨member.1, le_rfl⟩
    have firstTriangle := norm_add_le (firstSeparation time - (length : ℂ) * direction) ((length : ℂ) * direction)
    rw [sub_add_cancel, firstIdealNorm] at firstTriangle
    have secondTriangle := norm_add_le (secondSeparation time - (length : ℂ) * (-direction)) ((length : ℂ) * (-direction))
    rw [sub_add_cancel, secondIdealNorm] at secondTriangle
    have positiveTime : 0 ≤ frequency * time := mul_nonneg frequencyPositive.le member.1
    dsimp only [monitor]
    simp only [max_lt_iff]
    refine ⟨by linarith [upgraded.1], by linarith [upgraded.2.1], ?_⟩
    nlinarith [upgraded.2.2.1]
  have strict := strict_bootstrap_on_Icc monitorContinuous monitorInitial improvement
  have bootstrap (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖firstSeparation time‖ ≤ 2 * length ∧ ‖secondSeparation time‖ ≤ 2 * length ∧
        length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖ := by
    simpa only [monitor, max_le_iff, sub_nonpos] using (strict time member).le
  exact twoDipole_bootstrap_improvement frequencyPositive lengthPositive directionNorm initialDistanceLarge horizonNonnegative
    equation firstInitial secondInitial initialProjection initialUpper
    (fun time member => (bootstrap time member).1)
    (fun time member => (bootstrap time member).2.1)
    (fun time member => (bootstrap time member).2.2)

end EulerNonuniqueness.Section6
