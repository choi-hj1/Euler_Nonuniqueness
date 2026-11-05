import EulerNonuniqueness.Section3.CanonicalExteriorStaticPairRelative

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorStaticCoefficient_weight96_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 192 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖family.canonicalExteriorStaticCoefficient index time degree‖) ≤
      96 * weight / Real.pi := by
  have coefficientIdentity (degree : ℕ) : family.canonicalExteriorStaticCoefficient index time degree =
      exteriorVorticityCoefficient (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) (family.patch index).radius degree :=
    family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time degree positive separated
  simp_rw [coefficientIdentity]
  exact tsum_exteriorVorticityCoefficient_weight_le_uniform
    (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) _
    (family.patch index).radius_positive.le positive (by norm_num) weightNonnegative
    (family.subfamily_support_separated (Finset.univ.erase index)
      ((family.patch index).center time) time distance separated)
    (by norm_num; exact small) weightBound

theorem canonicalExteriorStaticCoefficient_higher_weight96_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 192 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    (∑' degree, (96 : ℝ) ^ (degree + 1) *
      ‖exteriorCoefficientWithoutLeading (family.canonicalExteriorStaticCoefficient index time) degree‖) ≤
      2 * (96 : ℝ) ^ 2 * (family.patch index).radius * weight / (Real.pi * distance) := by
  have coefficientIdentity (degree : ℕ) : family.canonicalExteriorStaticCoefficient index time degree =
      exteriorVorticityCoefficient (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) (family.patch index).radius degree :=
    family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius time degree positive separated
  have tailIdentity (degree : ℕ) :
      exteriorCoefficientWithoutLeading (family.canonicalExteriorStaticCoefficient index time) degree =
      exteriorHigherVorticityCoefficient (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) (family.patch index).radius degree := by
    unfold exteriorCoefficientWithoutLeading exteriorHigherVorticityCoefficient
    split_ifs
    · rfl
    · exact coefficientIdentity degree
  simp_rw [tailIdentity]
  exact tsum_exteriorHigherVorticityCoefficient_weight_le
    (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) _
    (family.patch index).radius_positive.le positive (by norm_num) weightNonnegative
    (family.subfamily_support_separated (Finset.univ.erase index)
      ((family.patch index).center time) time distance separated) (by linarith) weightBound

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
