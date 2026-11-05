import EulerNonuniqueness.Section6.PointComplexMomentAnisotropy
import EulerNonuniqueness.Section6.BoundaryQuadrupoleComplexMoment
import EulerNonuniqueness.Section6.PaperShapeBranch

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem conjugate_squared_direction_eq_phase {positive : ℂ} {phase : ℝ} (positiveNonzero : positive ≠ 0)
    (polar : positive = (‖positive‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) :
    star positive ^ 2 / ((‖positive‖ ^ 2 : ℝ) : ℂ) = Complex.exp (-2 * Complex.I * (phase : ℂ)) := by
  have normNonzero : (‖positive‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr positiveNonzero).ne'
  have starPolar : star positive = (‖positive‖ : ℂ) * Complex.exp (-Complex.I * (phase : ℂ)) := by
    calc
      star positive = star ((‖positive‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) := congrArg star polar
      _ = _ := by
        simp only [star_mul, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul]
        ring
  rw [starPolar, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  field_simp [normNonzero]
  congr 1
  ring

theorem exists_uniform_reference_complex_moment_phase_error :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error phase : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio → ∀ (index : Fin count),
      (∀ patch, BoundaryCloseToCircle scales motion time index patch error) → 0 ≤ error → error ≤ 1 / 16 →
      0 < diagonalDifference motion time index →
      0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im →
      |unstableShape motion time index| + |stableShape motion time index| < radius →
      positiveHalfDiagonal motion time index = (‖positiveHalfDiagonal motion time index‖ : ℂ) *
        Complex.exp (Complex.I * (phase : ℂ)) →
      ‖star (∫ position, quadrupoleDensity scales motion time index position •
          (position - quadrupoleCenter motion time index) ^ 2) -
        ((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference motion time index : ℝ) : ℂ) *
          Complex.exp (-2 * Complex.I * (phase : ℂ))‖ ≤
        2 * scales.circulation (index.val + 1) * constant * diagonalDifference motion time index *
          (|unstableShape motion time index| + |stableShape motion time index|) +
        512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error := by
  obtain ⟨constant, nonnegative, radius, radiusPositive, estimate⟩ := Section6.exists_uniform_point_complex_moment_phase_error
  refine ⟨constant, nonnegative, radius, radiusPositive, ?_⟩
  intro count scales motion horizon time error phase evolution inside amplitudePositive frequencyPositive ratioPositive index
    control errorNonnegative errorSmall differencePositive upper small polar
  let positive := positiveHalfDiagonal motion time index
  let negative := negativeHalfDiagonal motion time index
  let difference := diagonalDifference motion time index
  let circulation := scales.circulation (index.val + 1)
  have circulationPositive : 0 < circulation := scales.circulation_pos frequencyPositive ratioPositive _
  have normOrder : ‖negative‖ < ‖positive‖ := by
    change 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2 at differencePositive
    nlinarith [norm_nonneg positive, norm_nonneg negative]
  have positiveNonzero : positive ≠ 0 := norm_pos_iff.mp ((norm_nonneg negative).trans_lt normOrder)
  have chartIdentity := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have chartNorm : ‖Section6.pointShapeChart positive negative‖ ≤ |unstableShape motion time index| + |stableShape motion time index| := by
    change ‖Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)‖ ≤ _
    rw [chartIdentity, Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have core := estimate positive negative positiveNonzero normOrder (chartNorm.trans_lt small)
  have coreBound :
      ‖star (positive ^ 2 - negative ^ 2) - (Real.sqrt 2 : ℂ) * (difference : ℂ) *
        (star positive ^ 2 / ((‖positive‖ ^ 2 : ℝ) : ℂ))‖ ≤
      constant * difference * (|unstableShape motion time index| + |stableShape motion time index|) := by
    have rawDifferencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2 := differencePositive
    rw [abs_of_pos rawDifferencePositive] at core
    exact core.trans (mul_le_mul_of_nonneg_left chartNorm (mul_nonneg nonnegative differencePositive.le))
  have direction := conjugate_squared_direction_eq_phase positiveNonzero polar
  have pointIdentity : scales.circulation (index.val + 1) • Section6.fourPointCenteredComplexMoment
      (fun patch => patchCentroid motion time index patch) = (2 * circulation : ℂ) * (positive ^ 2 - negative ^ 2) := by
    rw [Section6.fourPointCenteredComplexMoment_eq_odd_difference, Complex.real_smul]
    change (circulation : ℂ) * (2 * (positive ^ 2 - negative ^ 2)) = _
    ring
  have patchError := evolution.quadrupole_complex_second_moment_point_error inside amplitudePositive frequencyPositive ratioPositive index
    control errorNonnegative errorSmall
  dsimp only at patchError
  rw [pointIdentity] at patchError
  have conjugatePatchError : ‖star (∫ position, quadrupoleDensity scales motion time index position •
      (position - quadrupoleCenter motion time index) ^ 2) - (2 * circulation : ℂ) * star (positive ^ 2 - negative ^ 2)‖ ≤
      512 * circulation * scales.radius (index.val + 1) ^ 2 * error := by
    have equality : star (∫ position, quadrupoleDensity scales motion time index position •
        (position - quadrupoleCenter motion time index) ^ 2) - (2 * circulation : ℂ) * star (positive ^ 2 - negative ^ 2) =
      star ((∫ position, quadrupoleDensity scales motion time index position • (position - quadrupoleCenter motion time index) ^ 2) -
        (2 * circulation : ℂ) * (positive ^ 2 - negative ^ 2)) := by
      simp only [star_sub, star_mul, Complex.star_def, map_mul, Complex.conj_ofReal, map_ofNat]
      ring
    rw [equality, norm_star]
    exact patchError
  have pointError : ‖(2 * circulation : ℂ) * star (positive ^ 2 - negative ^ 2) -
      ((2 * Real.sqrt 2 * circulation * difference : ℝ) : ℂ) * Complex.exp (-2 * Complex.I * (phase : ℂ))‖ ≤
      2 * circulation * constant * difference * (|unstableShape motion time index| + |stableShape motion time index|) := by
    have identity : (2 * circulation : ℂ) * star (positive ^ 2 - negative ^ 2) -
        ((2 * Real.sqrt 2 * circulation * difference : ℝ) : ℂ) * Complex.exp (-2 * Complex.I * (phase : ℂ)) =
      (2 * circulation : ℂ) * (star (positive ^ 2 - negative ^ 2) - (Real.sqrt 2 : ℂ) * (difference : ℂ) *
        (star positive ^ 2 / ((‖positive‖ ^ 2 : ℝ) : ℂ))) := by
      rw [direction]
      push_cast
      ring
    rw [identity, norm_mul]
    have scalarNorm : ‖(2 * circulation : ℂ)‖ = 2 * circulation := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos circulationPositive]
    rw [scalarNorm]
    exact (mul_le_mul_of_nonneg_left coreBound (by positivity)).trans_eq (by ring)
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (star (∫ position, quadrupoleDensity scales motion time index position • (position - quadrupoleCenter motion time index) ^ 2))
    ((2 * circulation : ℂ) * star (positive ^ 2 - negative ^ 2))
    (((2 * Real.sqrt 2 * circulation * difference : ℝ) : ℂ) * Complex.exp (-2 * Complex.I * (phase : ℂ)))
  exact triangle.trans ((add_le_add conjugatePatchError pointError).trans_eq (by ring))

end EulerNonuniqueness.Paper
