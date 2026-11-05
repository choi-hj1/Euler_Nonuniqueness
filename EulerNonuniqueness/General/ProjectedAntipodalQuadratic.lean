import EulerNonuniqueness.General.AntipodalQuadraticResonance

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticConjugate_antiperiodic_of_projected_antipodal
    (group : ℝ → Space →L[ℝ] Space) (projection : Space →L[ℝ] Space) {halfPeriod : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (leftHalf : projection.comp (group halfPeriod) = -projection)
    (rightHalf : (group halfPeriod).comp projection = -projection)
    (bilinear : BilinearEnd Space)
    (inputProjection : ∀ first second, bilinear (projection first) (projection second) = bilinear first second)
    (outputProjection : ∀ first second, projection (bilinear first second) = bilinear first second)
    (time : ℝ) :
    quadraticConjugate group (time + halfPeriod) bilinear = -quadraticConjugate group time bilinear := by
  have negativeHalf (value : Space) : group (-halfPeriod) (projection value) = -projection value := by
    have inverse := congrArg (fun operator : Space →L[ℝ] Space => operator (projection value))
      (addition (-halfPeriod) halfPeriod)
    have right := congrArg (fun operator : Space →L[ℝ] Space => operator value) rightHalf
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply] at right
    rw [neg_add_cancel, atZero] at inverse
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, right, map_neg] at inverse
    simpa only [neg_neg] using (congrArg (fun current : Space => -current) inverse).symm
  have projectedHalf (value : Space) : projection (group halfPeriod value) = -projection value :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) leftHalf
  have inputHalf (first second : Space) :
      bilinear (group halfPeriod first) (group halfPeriod second) = bilinear first second := by
    rw [← inputProjection (group halfPeriod first) (group halfPeriod second),
      projectedHalf, projectedHalf]
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    exact inputProjection first second
  ext first second
  change group (-(time + halfPeriod))
      (bilinear (group (time + halfPeriod) first) (group (time + halfPeriod) second)) =
    -group (-time) (bilinear (group time first) (group time second))
  rw [show time + halfPeriod = halfPeriod + time by ring, addition,
    show -(halfPeriod + time) = -time + -halfPeriod by ring, addition]
  simp only [ContinuousLinearMap.comp_apply]
  rw [inputHalf, ← outputProjection (group time first) (group time second), negativeHalf, map_neg]

theorem quadraticResonance_eq_zero_of_projected_antipodal
    (group : ℝ → Space →L[ℝ] Space) (generator projection : Space →L[ℝ] Space) {halfPeriod : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (leftHalf : projection.comp (group halfPeriod) = -projection)
    (rightHalf : (group halfPeriod).comp projection = -projection)
    (bilinear : BilinearEnd Space)
    (inputProjection : ∀ first second, bilinear (projection first) (projection second) = bilinear first second)
    (outputProjection : ∀ first second, projection (bilinear first second) = bilinear first second) :
    quadraticResonance group (2 * halfPeriod) bilinear = 0 := by
  have continuous : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time))
  have integralZero : (∫ time in (0 : ℝ)..(2 * halfPeriod), quadraticConjugate group time bilinear) = 0 := by
    with_reducible
      exact integral_double_antiperiod_eq_zero (Space := BilinearEnd Space) continuous
        (quadraticConjugate_antiperiodic_of_projected_antipodal group projection atZero addition
          leftHalf rightHalf bilinear inputProjection outputProjection)
  rw [quadraticResonance, integralZero]
  ext first second
  exact smul_zero _

end

end EulerNonuniqueness.General
