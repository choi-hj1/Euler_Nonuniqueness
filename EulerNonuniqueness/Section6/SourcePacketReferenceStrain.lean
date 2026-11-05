import EulerNonuniqueness.Section6.SourcePacketReferenceMoment
import EulerNonuniqueness.Section6.PaperPatchMomentStrainError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_literal_strain_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {threshold constant time distance : ℝ}
    (evolution : FinitePatchEvolution scales motion 2) (inside : time ∈ Icc 0 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4) (coarse : ReferenceCoarseBounds scales motion threshold constant)
    (source : Fin count) (location : ℂ) (distancePositive : 0 < distance)
    (locationFar : distance ≤ ‖location - quadrupoleCenter motion time source‖)
    (scaleSmall : 8 * scales.length (source.val + 1) ≤ distance)
    (neutralScaleSmall : constant * scales.hessian * scales.length (source.val + 1) ^ 2 * 2 *
      Real.exp (2 * (constant * scales.strain)) ≤ scales.length (source.val + 1))
    (radiusSmall : scales.radius (source.val + 1) *
      (1 + constant * (scales.omega (source.val + 1))⁻¹ ^ 2) ≤ scales.length (source.val + 1)) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) location‖ ≤
      4 * scales.circulation (source.val + 1) * ‖centroidAsymmetry motion time source‖ /
          (Real.pi * distance ^ 3) +
        3 * ‖∫ position, quadrupoleDensity scales motion time source position •
          (position - quadrupoleCenter motion time source) ^ 2‖ / (2 * Real.pi * distance ^ 4) +
        352 * scales.circulation (source.val + 1) * (4 * scales.length (source.val + 1)) ^ 3 /
          (Real.pi * distance ^ 5) := by
  have bounds := coarse.2.1 time inside source
  have lengthPositive := scales.length_pos (source.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have neutralBound : ‖centroidAsymmetry motion time source‖ ≤ scales.length (source.val + 1) := by
    apply bounds.2.2.2.2.1.trans (le_trans ?_ neutralScaleSmall)
    have exponentialBound : Real.exp (constant * scales.strain * time) ≤
        Real.exp (2 * (constant * scales.strain)) := Real.exp_le_exp.mpr (by
      convert mul_le_mul_of_nonneg_left inside.2 (mul_nonneg constantNonnegative strainNonnegative) using 1 <;> ring)
    exact mul_le_mul (mul_le_mul_of_nonneg_left inside.2 (by positivity)) exponentialBound
      (Real.exp_pos _).le (by positivity)
  have lengthSquarePositive := sq_pos_of_pos lengthPositive
  have differencePositive : 0 < diagonalDifference motion time source := by
    have lower := (le_div_iff₀ lengthSquarePositive).mp bounds.2.2.1
    nlinarith
  have differenceUpper : diagonalDifference motion time source ≤ 2 * scales.length (source.val + 1) ^ 2 :=
    (div_le_iff₀ lengthSquarePositive).mp bounds.2.2.2.1
  have radialUpper : radialShape motion time source ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    have first := (le_abs_self _).trans bounds.1
    have second := (le_abs_self _).trans bounds.2.1
    linarith
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape
    lengthPositive differencePositive differenceUpper radialUpper
  have bounded (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time source patch) :
      position ∈ Metric.closedBall (quadrupoleCenter motion time source) (4 * scales.length (source.val + 1)) := by
    have estimate := evolution.reference_domain_confinement inside source bounds.2.2.2.2.2
      (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _) positiveBound negativeBound neutralBound
      (center := quadrupoleCenter motion time source) (centerError := 0) (by simp) patch position member
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith
  have actual := evolution.quadrupole_strain_target_moment_error inside amplitudePositive frequencyPositive ratioPositive
    source (quadrupoleCenter motion time source) location 0 (by positivity) bounded
    (distancePositive.trans_le locationFar) (by linarith)
  simp only [mul_zero, zero_div, star_zero, sub_zero] at actual
  apply actual.trans
  gcongr

end EulerNonuniqueness.Paper
