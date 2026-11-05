import EulerNonuniqueness.General.PeriodicQuadraticHomological
import EulerNonuniqueness.General.AntiperiodicIntegral

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticConjugate_antiperiodic_of_antipodal
    (group : ℝ → Space →L[ℝ] Space) {halfPeriod : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (atHalf : group halfPeriod = -ContinuousLinearMap.id ℝ Space)
    (bilinear : BilinearEnd Space) (time : ℝ) :
    quadraticConjugate group (time + halfPeriod) bilinear = -quadraticConjugate group time bilinear := by
  have atNegative : group (-halfPeriod) = -ContinuousLinearMap.id ℝ Space := by
    have identity := addition (-halfPeriod) halfPeriod
    rw [neg_add_cancel, atZero, atHalf] at identity
    ext value
    have point := congrArg (fun operator : Space →L[ℝ] Space => operator value) identity
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, map_neg] at point
    have negPoint := congrArg (fun current : Space => -current) point
    simpa only [neg_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using negPoint.symm
  have forward : group (time + halfPeriod) = -group time := by
    rw [addition, atHalf]
    ext value
    simp
  have backward : group (-(time + halfPeriod)) = -group (-time) := by
    rw [show -(time + halfPeriod) = -halfPeriod + -time by ring, addition, atNegative]
    ext value
    simp
  ext first second
  simp [quadraticConjugate, bilinearPostcompose, forward, backward, addition, atHalf, atNegative]

theorem quadraticResonance_eq_zero_of_antipodal
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {halfPeriod : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (atHalf : group halfPeriod = -ContinuousLinearMap.id ℝ Space) (bilinear : BilinearEnd Space) :
    quadraticResonance group (2 * halfPeriod) bilinear = 0 := by
  have continuous : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time))
  have integralZero : (∫ time in (0 : ℝ)..(2 * halfPeriod), quadraticConjugate group time bilinear) = 0 := by
    with_reducible
      exact integral_double_antiperiod_eq_zero (Space := BilinearEnd Space) continuous
        (quadraticConjugate_antiperiodic_of_antipodal group atZero addition atHalf bilinear)
  rw [quadraticResonance, integralZero]
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change (1 / (2 * halfPeriod) : ℝ) • (0 : Space) = 0
  exact smul_zero _

end

end EulerNonuniqueness.General
