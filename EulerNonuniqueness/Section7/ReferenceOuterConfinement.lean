import EulerNonuniqueness.Section4.ReferenceConfinement

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem ReferenceSolution.outer_domain_confinement {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {phase : Fin count → ℝ} {threshold constant : ℝ}
    (reference : ReferenceSolution scales motion phase threshold constant)
    (thresholdSmall : threshold ≤ 1 / 4) (outer : Fin count) (outerIndex : outer.val = 0)
    (radiusPositive : 0 < scales.radius 1)
    (patchRadiusSmall : scales.radius 1 * (1 + constant * (scales.omega 1)⁻¹ ^ 2) ≤ 2 * scales.length 1)
    (asymmetrySmall : constant * scales.hessian * scales.length 1 ^ 2 *
      Real.exp (constant * scales.strain) ≤ scales.length 1)
    (centerSmall : constant * scales.outerDisplacementBound ≤ 1) :
    ∀ patch position, position ∈ motion.domain 1 outer patch →
      ‖position - (scales.location 1 : ℂ)‖ ≤ 6 * scales.length 1 := by
  obtain ⟨unstable, phaseLift, _, _, evolution, coarse, sharp⟩ := reference
  have atTime := coarse.2.1 1 (by norm_num) outer
  obtain ⟨unstableBound, stableBound, differenceLower, differenceUpper, asymmetryBound, boundaryBound⟩ := atTime
  have indexEquality : outer.val + 1 = 1 := by omega
  rw [indexEquality] at differenceLower differenceUpper asymmetryBound boundaryBound
  have lengthPositive := scales.length_pos 1
  have differencePositive : 0 < diagonalDifference motion 1 outer := by
    have lower := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp differenceLower
    nlinarith
  have differenceControl : diagonalDifference motion 1 outer ≤ 2 * scales.length 1 ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp differenceUpper
  have radialControl : radialShape motion 1 outer ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    have unstableUpper := (abs_le.mp unstableBound).2
    have stableUpper := (abs_le.mp stableBound).2
    linarith
  have diagonalControl := halfDiagonals_norm_le_of_reference_shape lengthPositive differencePositive
    differenceControl radialControl
  have asymmetryControl : ‖centroidAsymmetry motion 1 outer‖ ≤ scales.length 1 := by
    simpa only [mul_one] using asymmetryBound.trans (by simpa only [mul_one] using asymmetrySmall)
  have centerControl : ‖quadrupoleCenter motion 1 outer - (scales.location 1 : ℂ)‖ ≤ scales.length 1 := by
    have estimate := sharp.2 1 (by norm_num) outer outerIndex
    have control := (div_le_iff₀ lengthPositive).mp estimate
    exact control.trans (by nlinarith)
  intro patch position member
  have estimate := evolution.reference_domain_confinement (time := 1) (by norm_num) outer
    boundaryBound (by simpa only [indexEquality] using radiusPositive) diagonalControl.1 diagonalControl.2
    asymmetryControl centerControl patch position member
  rw [indexEquality] at estimate
  linarith

theorem ReferenceSolution.outer_domain_inside_separating_annulus {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {phase : Fin count → ℝ} {threshold constant : ℝ}
    (reference : ReferenceSolution scales motion phase threshold constant)
    (thresholdSmall : threshold ≤ 1 / 4) (outer : Fin count) (outerIndex : outer.val = 0)
    (radiusPositive : 0 < scales.radius 1)
    (patchRadiusSmall : scales.radius 1 * (1 + constant * (scales.omega 1)⁻¹ ^ 2) ≤ 2 * scales.length 1)
    (asymmetrySmall : constant * scales.hessian * scales.length 1 ^ 2 *
      Real.exp (constant * scales.strain) ≤ scales.length 1)
    (centerSmall : constant * scales.outerDisplacementBound ≤ 1) (frequencyLarge : 192 ≤ scales.omega 1) :
    ∀ patch position, position ∈ motion.domain 1 outer patch →
      ‖position - (scales.location 1 : ℂ)‖ ≤ scales.omega 1 * scales.length 1 / 32 := by
  intro patch position member
  have estimate := reference.outer_domain_confinement thresholdSmall outer outerIndex radiusPositive
    patchRadiusSmall asymmetrySmall centerSmall patch position member
  have scaled := mul_le_mul_of_nonneg_right frequencyLarge (scales.length_pos 1).le
  linarith

end EulerNonuniqueness.Paper
