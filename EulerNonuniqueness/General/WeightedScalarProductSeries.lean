import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

noncomputable section

namespace EulerNonuniqueness.General

theorem norm_tsum_smul_sub_tsum_smul_le_weighted {Index Scalar Space : Type*}
    [NormedField Scalar] [NormedAddCommGroup Space] [NormedSpace Scalar Space] [CompleteSpace Space]
    (firstCoefficients secondCoefficients : Index → Scalar) (firstVectors secondVectors : Index → Space)
    (weight : Index → ℝ)
    {constant differenceBudget finalBudget : ℝ}
    (firstSummable : Summable (fun index => weight index * ‖firstCoefficients index‖))
    (secondSummable : Summable (fun index => weight index * ‖secondCoefficients index‖))
    (differenceSummable : Summable (fun index => weight index * ‖firstCoefficients index - secondCoefficients index‖))
    (vectorDifference : ∀ index, ‖firstVectors index - secondVectors index‖ ≤ constant * weight index * differenceBudget)
    (finalVector : ∀ index, ‖secondVectors index‖ ≤ constant * weight index * finalBudget) :
    Summable (fun index => firstCoefficients index • firstVectors index) ∧
    Summable (fun index => secondCoefficients index • secondVectors index) ∧
      ‖(∑' index, firstCoefficients index • firstVectors index) -
        (∑' index, secondCoefficients index • secondVectors index)‖ ≤
        constant * ((∑' index, weight index * ‖firstCoefficients index‖) * differenceBudget +
          (∑' index, weight index * ‖firstCoefficients index - secondCoefficients index‖) * finalBudget) := by
  have firstVector (index : Index) : ‖firstVectors index‖ ≤ constant * weight index * (differenceBudget + finalBudget) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (firstVectors index) (secondVectors index) 0
    simp only [sub_zero] at triangle
    exact triangle.trans ((add_le_add (vectorDifference index) (finalVector index)).trans_eq (by ring))
  have firstActual : Summable (fun index => firstCoefficients index • firstVectors index) := by
    apply Summable.of_norm_bounded _ (firstSummable.mul_right (constant * (differenceBudget + finalBudget)))
    intro index
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (firstVector index) (norm_nonneg _)).trans_eq (by ring)
  have secondActual : Summable (fun index => secondCoefficients index • secondVectors index) := by
    apply Summable.of_norm_bounded _ (secondSummable.mul_right (constant * finalBudget))
    intro index
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (finalVector index) (norm_nonneg _)).trans_eq (by ring)
  have differenceBound (index : Index) :
      ‖firstCoefficients index • firstVectors index - secondCoefficients index • secondVectors index‖ ≤
        constant * ((weight index * ‖firstCoefficients index‖) * differenceBudget +
          (weight index * ‖firstCoefficients index - secondCoefficients index‖) * finalBudget) := by
    have identity : firstCoefficients index • firstVectors index - secondCoefficients index • secondVectors index =
        firstCoefficients index • (firstVectors index - secondVectors index) +
          (firstCoefficients index - secondCoefficients index) • secondVectors index := by
      rw [smul_sub, sub_smul]
      abel
    rw [identity]
    have firstTerm : ‖firstCoefficients index • (firstVectors index - secondVectors index)‖ ≤
        ‖firstCoefficients index‖ * (constant * weight index * differenceBudget) := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (vectorDifference index) (norm_nonneg _)
    have secondTerm : ‖(firstCoefficients index - secondCoefficients index) • secondVectors index‖ ≤
        ‖firstCoefficients index - secondCoefficients index‖ * (constant * weight index * finalBudget) := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (finalVector index) (norm_nonneg _)
    exact (norm_add_le _ _).trans ((add_le_add firstTerm secondTerm).trans_eq (by ring))
  have majorant := ((firstSummable.mul_right differenceBudget).add
    (differenceSummable.mul_right finalBudget)).mul_left constant
  have normSummable := Summable.of_nonneg_of_le (fun index => norm_nonneg
    (firstCoefficients index • firstVectors index - secondCoefficients index • secondVectors index)) differenceBound majorant
  refine ⟨firstActual, secondActual, ?_⟩
  rw [← firstActual.tsum_sub secondActual]
  apply (norm_tsum_le_tsum_norm normSummable).trans
  have estimate := normSummable.tsum_le_tsum differenceBound majorant
  rw [tsum_mul_left, (firstSummable.mul_right differenceBudget).tsum_add
    (differenceSummable.mul_right finalBudget), tsum_mul_right, tsum_mul_right] at estimate
  exact estimate

end EulerNonuniqueness.General
