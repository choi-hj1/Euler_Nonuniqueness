import EulerNonuniqueness.Section3.RelabeledExteriorHigherPrimitive
import EulerNonuniqueness.Section3.MovingStrainPrimitiveFormula

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem relabeledDiskForcingPrimitive_leading_realification (angular : PeriodicC1HolderHalf)
    (frequency : ℝ) (amplitude : ℝ → ℂ) (time : ℝ) :
    relabeledDiskForcingPrimitive angular 0 frequency amplitude time =
      frequency⁻¹ • movingStrainRealPrimitiveValue (diskRelabelCurve angular 1)
        (diskForcingPhase 0 frequency time * amplitude time) := by
  rw [movingStrainRealPrimitiveValue_formula]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (diskForcingPrimitiveFactor 0 frequency * amplitude time * diskForcingPhase 0 frequency time) *
      star ((c1NaturalPower (diskRelabelCurve angular 1) 1).val.1 label) =
    ((frequency⁻¹ : ℝ) : ℂ) * ((2 * Complex.I * (diskForcingPhase 0 frequency time * amplitude time)) *
      star ((diskRelabelCurve angular 1).val.1 label))
  rw [c1NaturalPower_one]
  simp only [diskForcingPrimitiveFactor, Nat.reduceAdd, Nat.cast_one, one_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem relabeledForcingPrimitiveSeries_without_leading (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun power => (2 : ℝ) ^ (power + 1) * ‖amplitude power time‖)) :
    relabeledForcingPrimitiveSeries angular frequency
        (fun power current => exteriorCoefficientWithoutLeading (fun degree => amplitude degree current) power) time =
      relabeledForcingPrimitiveSeries angular frequency amplitude time -
        frequency⁻¹ • movingStrainRealPrimitiveValue (diskRelabelCurve angular 1)
          (diskForcingPhase 0 frequency time * amplitude 0 time) := by
  have fullCircle := diskForcingPrimitive_summable nonzero amplitude time weighted
  have fullSum := (fixedRelabelEquivalence angular small).toContinuousLinearMap.hasSum fullCircle.hasSum
  simp only [ContinuousLinearEquiv.coe_coe, fixedRelabelEquivalence_forcingPrimitive angular small realValues] at fullSum
  have single := hasSum_ite_eq (0 : ℕ) (relabeledDiskForcingPrimitive angular 0 frequency (amplitude 0) time)
  have tailSum : HasSum (fun power => relabeledDiskForcingPrimitive angular power frequency
      (fun current => exteriorCoefficientWithoutLeading (fun degree => amplitude degree current) power) time)
      (fixedRelabelEquivalence angular small (∑' power, diskForcingPrimitive power frequency (amplitude power) time) -
        relabeledDiskForcingPrimitive angular 0 frequency (amplitude 0) time) := by
    convert fullSum.sub single using 1
    funext power
    by_cases zero : power = 0
    · subst power
      simp only [exteriorCoefficientWithoutLeading, ite_true, relabeledDiskForcingPrimitive, mul_zero, zero_mul, zero_smul, sub_self]
    · simp only [exteriorCoefficientWithoutLeading, if_neg zero, sub_zero]
  rw [relabeledForcingPrimitiveSeries_fixedRelabel angular small realValues nonzero amplitude time weighted,
    relabeledDiskForcingPrimitive_leading_realification] at tailSum
  exact tailSum.tsum_eq

namespace FiniteMovingPatchFamily

theorem relabeledExteriorHigherForcingPrimitive_eq_sub_leading {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (small : 2 * (family.patch index).radius / distance < 1) :
    family.relabeledExteriorHigherForcingPrimitive index angular frequency time =
      family.relabeledExteriorForcingPrimitive index angular frequency time - frequency⁻¹ •
        movingStrainRealPrimitiveValue (diskRelabelCurve angular 1)
          (diskForcingPhase 0 frequency time * family.exteriorTaylorCoefficient (Finset.univ.erase index)
            (family.patch index).center (family.patch index).radius 1 time) :=
  relabeledForcingPrimitiveSeries_without_leading angular angularSmall realValues nonzero _ time
    (family.summable_weighted_exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius time (family.patch index).radius_positive.le positive separated small)

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
