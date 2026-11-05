import EulerNonuniqueness.Section3.MovingContourRotatedCrossBounds

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingRawHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingRawC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem complexSMulC1_difference_norm (scalar : ℂ) (first second : PeriodicC1HolderHalf) :
    ‖scalar • first - scalar • second‖ = ‖scalar‖ * ‖first - second‖ := by
  have identity : scalar • first - scalar • second = scalar • (first - second) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change scalar * first.val.1 label - scalar * second.val.1 label = scalar * (first.val.1 label - second.val.1 label)
    ring
  rw [identity, complexSMulC1_norm]

def FiniteContourConfiguration.movingRawNormBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap : ℝ) (index : Fin count) : ℝ :=
  |configuration.density index| * contourVelocityBanachBound shapeRadius +
    (∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
      configuration.movingCrossNormBound centerBound gap) + 3 * |configuration.density index / 2|

def FiniteContourConfiguration.movingRawLipschitzBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap : ℝ) (index : Fin count) : ℝ :=
  |configuration.density index| * contourVelocityBanachLipschitzConstant shapeRadius +
    (∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
      (configuration.movingCrossLipschitzBound centerBound gap index other +
        |configuration.density index / 2| * configuration.movingCrossNormBound centerBound gap)) +
    |configuration.density index / 2|

theorem FiniteContourConfiguration.movingStateRawField_uniform_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (shapeNonnegative : 0 ≤ shapeRadius)
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi))) {state : MovingContourState count}
    (inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) (index : Fin count) :
    ‖configuration.movingStateRawField state index‖ ≤ configuration.movingRawNormBound centerBound shapeRadius gap index := by
  have selfBound : ‖configuration.density index • extendedContourVelocity (state.2.2 index)‖ ≤
      |configuration.density index| * contourVelocityBanachBound shapeRadius := by
    rw [norm_smul (configuration.density index) (extendedContourVelocity (state.2.2 index)), Real.norm_eq_abs,
      extendedContourVelocity_eq (state.2.2 index) ((inside.2.1 index).trans_lt shapeSmall)]
    exact mul_le_mul_of_nonneg_left
      (contourVelocityBanach_uniform_norm_bound (state.2.2 index) shapeNonnegative shapeSmall (inside.2.1 index)) (abs_nonneg _)
  have crossBound : ‖∑ other ∈ Finset.univ.erase index,
      (configuration.density other / configuration.radius index) • configuration.movingRotatedCrossField state index other‖ ≤
      ∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
        configuration.movingCrossNormBound centerBound gap := by
    apply (norm_sum_le (Finset.univ.erase index)
      (fun other => (configuration.density other / configuration.radius index) • configuration.movingRotatedCrossField state index other)).trans
    apply Finset.sum_le_sum
    intro other member
    rw [norm_smul (configuration.density other / configuration.radius index)
      (configuration.movingRotatedCrossField state index other), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (configuration.movingRotatedCrossField_uniform_norm_bound positive (shapeSmall.trans_le (min_le_left _ _)).le
        inside index other (Finset.ne_of_mem_erase member).symm) (abs_nonneg _)
  have rotationBound : ‖(configuration.density index / 2) • ((Complex.I : ℂ) • state.2.2 index)‖ ≤
      3 * |configuration.density index / 2| := by
    rw [norm_smul (configuration.density index / 2) ((Complex.I : ℂ) • state.2.2 index),
      Real.norm_eq_abs, complexSMulC1_norm, Complex.norm_I, one_mul]
    have actual := mul_le_mul_of_nonneg_left
      (configuration.movingStateAdmissible_shapes_bounded (shapeSmall.trans_le (min_le_left _ _)).le inside index) (abs_nonneg (configuration.density index / 2))
    nlinarith
  change ‖(configuration.density index • extendedContourVelocity (state.2.2 index) +
    ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      configuration.movingRotatedCrossField state index other) -
      (configuration.density index / 2) • ((Complex.I : ℂ) • state.2.2 index)‖ ≤ _
  apply (norm_sub_le
    (configuration.density index • extendedContourVelocity (state.2.2 index) +
      ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) • configuration.movingRotatedCrossField state index other)
    ((configuration.density index / 2) • ((Complex.I : ℂ) • state.2.2 index))).trans
  exact add_le_add
    ((norm_add_le (configuration.density index • extendedContourVelocity (state.2.2 index))
      (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) • configuration.movingRotatedCrossField state index other)).trans
      (add_le_add selfBound crossBound)) rotationBound

theorem FiniteContourConfiguration.movingStateRawField_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap : ℝ}
    (positive : 0 < gap) (centerNonnegative : 0 ≤ centerBound) (shapeNonnegative : 0 ≤ shapeRadius)
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi)))
    {first second : MovingContourState count}
    (firstInside : first ∈ configuration.movingStateAdmissible centerBound shapeRadius gap)
    (secondInside : second ∈ configuration.movingStateAdmissible centerBound shapeRadius gap) (index : Fin count) :
    ‖configuration.movingStateRawField first index - configuration.movingStateRawField second index‖ ≤
      configuration.movingRawLipschitzBound centerBound shapeRadius gap index * ‖first - second‖ := by
  have selfBound : ‖configuration.density index •
      (extendedContourVelocity (first.2.2 index) - extendedContourVelocity (second.2.2 index))‖ ≤
      |configuration.density index| * contourVelocityBanachLipschitzConstant shapeRadius * ‖first - second‖ := by
    rw [norm_smul (configuration.density index)
      (extendedContourVelocity (first.2.2 index) - extendedContourVelocity (second.2.2 index)), Real.norm_eq_abs,
      extendedContourVelocity_eq (first.2.2 index) ((firstInside.2.1 index).trans_lt shapeSmall),
      extendedContourVelocity_eq (second.2.2 index) ((secondInside.2.1 index).trans_lt shapeSmall)]
    have actual := contourVelocityBanach_parameter_norm_bound (first.2.2 index) (second.2.2 index)
      shapeNonnegative shapeSmall (firstInside.2.1 index) (secondInside.2.1 index)
    have enlarged := actual.trans (mul_le_mul_of_nonneg_left (movingContourState_shape_norm_sub_le first second index)
      (contourVelocityBanachLipschitzConstant_nonneg shapeNonnegative shapeSmall))
    exact (mul_le_mul_of_nonneg_left enlarged (abs_nonneg _)).trans_eq (by ring)
  have crossBound : ‖∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other)‖ ≤
      (∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
        (configuration.movingCrossLipschitzBound centerBound gap index other +
          |configuration.density index / 2| * configuration.movingCrossNormBound centerBound gap)) * ‖first - second‖ := by
    apply (norm_sum_le (Finset.univ.erase index) (fun other => (configuration.density other / configuration.radius index) •
      (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other))).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro other member
    rw [norm_smul (configuration.density other / configuration.radius index)
      (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other), Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (configuration.movingRotatedCrossField_parameter_norm_bound positive centerNonnegative
      (shapeSmall.trans_le (min_le_left _ _)).le firstInside secondInside index other (Finset.ne_of_mem_erase member).symm)
      (abs_nonneg _)).trans_eq (by ring)
  have rotationBound : ‖(configuration.density index / 2) •
      ((Complex.I : ℂ) • first.2.2 index - (Complex.I : ℂ) • second.2.2 index)‖ ≤
      |configuration.density index / 2| * ‖first - second‖ := by
    rw [norm_smul (configuration.density index / 2)
      ((Complex.I : ℂ) • first.2.2 index - (Complex.I : ℂ) • second.2.2 index), Real.norm_eq_abs,
      complexSMulC1_difference_norm, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left (movingContourState_shape_norm_sub_le first second index) (abs_nonneg _)
  have identity : configuration.movingStateRawField first index - configuration.movingStateRawField second index =
      (configuration.density index • (extendedContourVelocity (first.2.2 index) - extendedContourVelocity (second.2.2 index)) +
        ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other)) -
      (configuration.density index / 2) • ((Complex.I : ℂ) • first.2.2 index - (Complex.I : ℂ) • second.2.2 index) := by
    have sumIdentity :
        (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other)) =
        (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          configuration.movingRotatedCrossField first index other) -
        ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          configuration.movingRotatedCrossField second index other := by
      rw [← Finset.sum_sub_distrib (s := Finset.univ.erase index)
        (f := fun other => (configuration.density other / configuration.radius index) • configuration.movingRotatedCrossField first index other)
        (g := fun other => (configuration.density other / configuration.radius index) • configuration.movingRotatedCrossField second index other)]
      apply Finset.sum_congr rfl
      intro other _member
      exact smul_sub (configuration.density other / configuration.radius index)
        (configuration.movingRotatedCrossField first index other) (configuration.movingRotatedCrossField second index other)
    rw [sumIdentity]
    rw [smul_sub (configuration.density index) (extendedContourVelocity (first.2.2 index)) (extendedContourVelocity (second.2.2 index)),
      smul_sub (configuration.density index / 2) ((Complex.I : ℂ) • first.2.2 index) ((Complex.I : ℂ) • second.2.2 index)]
    unfold FiniteContourConfiguration.movingStateRawField FiniteContourConfiguration.movingRotatedCrossField
    abel
  rw [identity]
  apply (norm_sub_le
    (configuration.density index • (extendedContourVelocity (first.2.2 index) - extendedContourVelocity (second.2.2 index)) +
      ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
        (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other))
    ((configuration.density index / 2) • ((Complex.I : ℂ) • first.2.2 index - (Complex.I : ℂ) • second.2.2 index))).trans
  apply (add_le_add
    ((norm_add_le (configuration.density index • (extendedContourVelocity (first.2.2 index) - extendedContourVelocity (second.2.2 index)))
      (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
        (configuration.movingRotatedCrossField first index other - configuration.movingRotatedCrossField second index other))).trans
      (add_le_add selfBound crossBound)) rotationBound).trans_eq
  unfold FiniteContourConfiguration.movingRawLipschitzBound
  ring

end EulerNonuniqueness.Paper
