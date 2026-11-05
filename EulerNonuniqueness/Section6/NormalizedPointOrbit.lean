import EulerNonuniqueness.Section6.OutgoingSectionStability

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem normalizedSeparatingOrbit_point_nonzero (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (time : ℝ) :
    orbit.positive time ≠ 0 ∧ orbit.negative time ≠ 0 ∧
      orbit.positive time - orbit.negative time ≠ 0 ∧
      orbit.positive time + orbit.negative time ≠ 0 := by
  obtain ⟨distanceMin, distancePositive, estimate⟩ := normalized.2.2.1
  have properties := estimate time
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro zero
    rw [zero, norm_zero] at properties
    linarith [properties.1]
  · intro zero
    rw [zero, norm_zero] at properties
    linarith [properties.2.1]
  · intro zero
    rw [zero, norm_zero] at properties
    linarith [properties.2.2.1]
  · intro zero
    rw [zero, norm_zero] at properties
    linarith [properties.2.2.2]

theorem normalizedSeparatingOrbit_full_point_equation (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (time : ℝ) :
    HasDerivAt (fun current => centrallySymmetricFourPoint
      (orbit.positive current) (-orbit.negative current))
      (fourPointField 1 (centrallySymmetricFourPoint
        (orbit.positive time) (-orbit.negative time))) time ∧
    FourPointNoncollision (centrallySymmetricFourPoint
      (orbit.positive time) (-orbit.negative time)) := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    normalizedSeparatingOrbit_point_nonzero orbit normalized time
  have negativeNonzero' : -orbit.negative time ≠ 0 := neg_ne_zero.mpr negativeNonzero
  have differenceNonzero' : orbit.positive time - -orbit.negative time ≠ 0 := by
    simpa only [sub_neg_eq_add] using sumNonzero
  have sumNonzero' : orbit.positive time + -orbit.negative time ≠ 0 := by
    simpa only [← sub_eq_add_neg] using differenceNonzero
  have positiveDerivative : HasDerivAt orbit.positive
      (positivePointVelocity 1 (orbit.positive time) (orbit.negative time)) time := by
    simpa only [positivePointVelocity, Complex.ofReal_one, mul_one] using (normalized.2.1 time).2.2.1
  have negativeDerivative : HasDerivAt orbit.negative
      (negativePointVelocity 1 (orbit.positive time) (orbit.negative time)) time := by
    simpa only [negativePointVelocity, Complex.ofReal_one, mul_one] using (normalized.2.1 time).2.2.2
  have positiveFlip : positivePointVelocity 1 (orbit.positive time) (-orbit.negative time) =
      positivePointVelocity 1 (orbit.positive time) (orbit.negative time) := by
    simp [positivePointVelocity]
  have negativeFlip : negativePointVelocity 1 (orbit.positive time) (-orbit.negative time) =
      -negativePointVelocity 1 (orbit.positive time) (orbit.negative time) := by
    simp [negativePointVelocity]
    ring
  refine ⟨?_, centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero'
    differenceNonzero' sumNonzero'⟩
  rw [fourPointField_central_embedding 1 positiveNonzero negativeNonzero' differenceNonzero' sumNonzero',
    positiveFlip, negativeFlip]
  apply hasDerivAt_pi.mpr
  intro target
  fin_cases target
  · simpa [centrallySymmetricFourPoint] using positiveDerivative
  · simpa [centrallySymmetricFourPoint] using positiveDerivative.neg
  · simpa [centrallySymmetricFourPoint] using negativeDerivative.neg
  · simpa [centrallySymmetricFourPoint] using negativeDerivative

end EulerNonuniqueness.Section6
