import EulerNonuniqueness.Section4.ReferenceInitialShapeCoordinates
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound
import EulerNonuniqueness.Section6.PaperPatchAngularInertia
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem initialDiagonals_diagonalDifference (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) :
    ‖initialPositiveDiagonal scales index phase unstable‖ ^ 2 -
      ‖initialNegativeDiagonal scales index phase unstable‖ ^ 2 = scales.length index ^ 2 := by
  let ratio := rhombusRatio * (1 + unstable)
  have ratioPositive : 0 < ratio :=
    mul_pos reference_rhombusRatio_bounds.1 (by linarith [(abs_le.mp small).1])
  have ratioSmall : ratio < 1 := by
    dsimp only [ratio]
    nlinarith [reference_rhombusRatio_bounds.1, reference_rhombusRatio_bounds.2, (abs_le.mp small).1, (abs_le.mp small).2]
  have denominatorPositive : 0 < Real.sqrt (1 - ratio) := Real.sqrt_pos.mpr (by linarith)
  have rotationNorm (angle : ℝ) : ‖Complex.exp (Complex.I * (angle : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have positiveNorm : ‖initialPositiveDiagonal scales index phase unstable‖ =
      scales.length index / Real.sqrt (1 - ratio) := by
    rw [initialPositiveDiagonal, norm_div, norm_mul, rotationNorm, mul_one,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (scales.length_pos index).le,
      Real.norm_of_nonneg denominatorPositive.le]
  have negativeNorm : ‖initialNegativeDiagonal scales index phase unstable‖ =
      scales.length index * Real.sqrt ratio / Real.sqrt (1 - ratio) := by
    rw [initialNegativeDiagonal, norm_mul, rotationNorm, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (scales.length_pos index).le (Real.sqrt_nonneg _)) denominatorPositive.le)]
  rw [positiveNorm, negativeNorm, div_pow, div_pow, mul_pow,
    Real.sq_sqrt ratioPositive.le, Real.sq_sqrt (by linarith : 0 ≤ 1 - ratio)]
  field_simp [show 1 - ratio ≠ 0 by linarith]
  <;> ring

namespace FinitePatchEvolution

variable {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon threshold : ℝ}
variable (evolution : FinitePatchEvolution scales motion horizon) (horizonNonnegative : 0 ≤ horizon)
variable (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
variable (ratioPositive : 0 < scales.ratio) {phase unstable : Fin count → ℝ}
variable (initial : ReferenceInitialDisks scales motion phase unstable threshold)

include evolution horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial

theorem reference_initial_diagonalDifference (thresholdSmall : threshold ≤ 1 / 2) (index : Fin count) :
    diagonalDifference motion 0 index = scales.length (index.val + 1) ^ 2 := by
  have diagonals := evolution.reference_initial_diagonals horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index
  rw [diagonalDifference, diagonals.1, diagonals.2]
  exact initialDiagonals_diagonalDifference scales _ _ _ ((initial index).1.trans thresholdSmall)

theorem reference_initial_center_and_asymmetry (index : Fin count) :
    quadrupoleCenter motion 0 index = (scales.location (index.val + 1) : ℂ) ∧
      centroidAsymmetry motion 0 index = 0 := by
  have centroid := evolution.reference_initial_centroid horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index
  constructor <;> simp only [quadrupoleCenter, centroidAsymmetry, Fin.sum_univ_four,
    centroid, initialDiskCenter, Fin.reduceEq, if_true, if_false] <;> ring

theorem reference_initial_signed_first_moment (index : Fin count) (center : ℂ) :
    (∫ position, quadrupoleDensity scales motion 0 index position • (position - center)) = 0 := by
  rw [evolution.integral_quadrupoleDensity_first_moment ⟨le_rfl, horizonNonnegative⟩
    amplitudePositive frequencyPositive ratioPositive index center,
    (evolution.reference_initial_center_and_asymmetry horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index).2,
    smul_zero]

theorem reference_initial_normalizedBoundary (index : Fin count) (patch : Fin 4) (angle : ℝ) :
    normalizedBoundary scales motion 0 index patch angle = Complex.exp (Complex.I * (angle : ℂ)) := by
  have centroid := evolution.reference_initial_centroid horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index patch
  have boundary := ((initial index).2 patch).2 angle
  have radiusNonzero : (scales.radius (index.val + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _).ne'
  rw [normalizedBoundary, boundary, centroid]
  simp only [mul_zero, zero_div, Complex.ofReal_zero, neg_mul, mul_zero, neg_zero, Complex.exp_zero,
    one_mul, add_sub_cancel_left]
  exact mul_div_cancel_left₀ _ radiusNonzero

theorem reference_initial_boundaryCloseToCircle (index : Fin count) (patch : Fin 4) :
    BoundaryCloseToCircle scales motion 0 index patch 0 := by
  refine ⟨fun _ => 0, fun _ => rfl, hasC1HalfBound_zero.mono (by norm_num), ?_⟩
  have identity : (fun angle => normalizedBoundary scales motion 0 index patch angle -
      Complex.exp (Complex.I * (angle + (0 : ℝ) : ℝ))) = fun _ => (0 : ℂ) := by
    funext angle
    rw [evolution.reference_initial_normalizedBoundary horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index patch angle]
    simp
  rw [identity]
  exact hasC1HalfBound_zero

theorem reference_initial_angularImpulse (thresholdSmall : threshold ≤ 1 / 2) (index : Fin count) :
    angularImpulse scales motion 0 index = 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2 := by
  have estimate := evolution.quadrupole_angular_inertia_bound_of_boundaryControl ⟨le_rfl, horizonNonnegative⟩
    amplitudePositive frequencyPositive ratioPositive index
    (evolution.reference_initial_boundaryCloseToCircle horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index)
    (le_refl 0) (by norm_num)
  rw [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at estimate
  have equality := sub_eq_zero.mp (abs_nonpos_iff.mp estimate)
  rw [evolution.reference_initial_diagonalDifference horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial thresholdSmall index] at equality
  exact equality

end FinitePatchEvolution

end EulerNonuniqueness.Paper
