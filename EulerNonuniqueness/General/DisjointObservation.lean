import EulerNonuniqueness.General.Observation
import Mathlib

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace MeasureTheory

theorem abs_finset_sum_eq_sum_abs_of_disjoint_support
    {Domain Index : Type*} {fields : Index → Domain → ℝ} (indices : Finset Index)
    (disjoint : ∀ first ∈ indices, ∀ second ∈ indices, first ≠ second →
      Disjoint (Function.support (fields first)) (Function.support (fields second))) (point : Domain) :
    |∑ index ∈ indices, fields index point| = ∑ index ∈ indices, |fields index point| := by
  classical
  by_cases nonzero : ∃ index ∈ indices, fields index point ≠ 0
  · obtain ⟨selected, selectedInside, selectedNonzero⟩ := nonzero
    have others (index : Index) (inside : index ∈ indices) (different : index ≠ selected) : fields index point = 0 := by
      by_contra indexNonzero
      exact Set.disjoint_left.mp (disjoint index inside selected selectedInside different) indexNonzero selectedNonzero
    have sumEqual : (∑ index ∈ indices, fields index point) = fields selected point :=
      Finset.sum_eq_single selected others (fun outside => (outside selectedInside).elim)
    have absoluteSumEqual : (∑ index ∈ indices, |fields index point|) = |fields selected point| :=
      Finset.sum_eq_single selected (fun index inside different => by rw [others index inside different, abs_zero])
        (fun outside => (outside selectedInside).elim)
    rw [sumEqual, absoluteSumEqual]
  · have zero (index : Index) (inside : index ∈ indices) : fields index point = 0 := by
      by_contra nonzeroValue
      exact nonzero ⟨index, inside, nonzeroValue⟩
    have sumZero : (∑ index ∈ indices, fields index point) = 0 :=
      Finset.sum_eq_zero fun index inside => zero index inside
    rw [sumZero, abs_zero]
    symm
    exact Finset.sum_eq_zero fun index inside => by rw [zero index inside, abs_zero]

theorem weightedAbsIntegral_finset_sum_of_disjoint_support
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {fields : Index → Domain → ℝ} {weight : Domain → ℝ} (indices : Finset Index)
    (measurable : AEStronglyMeasurable weight measure)
    (bounded : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (integrable : ∀ index ∈ indices, Integrable (fields index) measure)
    (disjoint : ∀ first ∈ indices, ∀ second ∈ indices, first ≠ second →
      Disjoint (Function.support (fields first)) (Function.support (fields second))) :
    weightedAbsIntegral measure weight (∑ index ∈ indices, fields index) =
      ∑ index ∈ indices, weightedAbsIntegral measure weight (fields index) := by
  unfold weightedAbsIntegral
  simp only [Finset.sum_apply, abs_finset_sum_eq_sum_abs_of_disjoint_support indices disjoint, Finset.mul_sum]
  exact integral_finset_sum _ (fun index inside => integrable_weightedAbs measurable bounded (integrable index inside))

theorem weightedAbsIntegral_eq_integral_abs_of_one_on_support
    {Domain : Type*} [MeasurableSpace Domain] (measure : Measure Domain)
    {weight function : Domain → ℝ} (oneOn : ∀ point ∈ Function.support function, weight point = 1) :
    weightedAbsIntegral measure weight function = ∫ point, |function point| ∂measure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    change weight point * |function point| = |function point|
    by_cases nonzero : function point ≠ 0
    · rw [oneOn point nonzero, one_mul]
    · simp only [not_not.mp nonzero, abs_zero, mul_zero]

theorem weightedAbsIntegral_eq_zero_of_zero_on_support
    {Domain : Type*} [MeasurableSpace Domain] (measure : Measure Domain)
    {weight function : Domain → ℝ} (zeroOn : ∀ point ∈ Function.support function, weight point = 0) :
    weightedAbsIntegral measure weight function = 0 := by
  unfold weightedAbsIntegral
  have zero (point : Domain) : weight point * |function point| = 0 := by
    by_cases nonzero : function point ≠ 0
    · rw [zeroOn point nonzero, zero_mul]
    · simp only [not_not.mp nonzero, abs_zero, mul_zero]
  simp only [zero, integral_zero]

end MeasureTheory
