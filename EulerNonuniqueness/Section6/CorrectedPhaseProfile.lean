import EulerNonuniqueness.Section6.HalfDiagonalProfileRegularity
import EulerNonuniqueness.Section6.PhaseStraightening
import EulerNonuniqueness.Section6.NormalFormInverseMatching

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem complex_phase_exp_norm_sub_le (first second : ℝ) :
    ‖Complex.exp (Complex.I * (first : ℂ)) - Complex.exp (Complex.I * (second : ℂ))‖ ≤ |first - second| := by
  have equation (time : ℝ) : HasDerivAt (fun current : ℝ => Complex.exp (Complex.I * (current : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (time : ℂ))) time := by
    have argument := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time (hasDerivAt_id time)).const_mul Complex.I
    convert argument.cexp using 1 <;> simp [Function.comp_def, mul_comm]
  have bound (time : ℝ) : ‖Complex.I * Complex.exp (Complex.I * (time : ℂ))‖ ≤ (1 : ℝ) := by
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_self, Real.exp_zero, le_refl]
  simpa only [one_mul, Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun time (_ : time ∈ (univ : Set ℝ)) => (equation time).hasDerivWithinAt)
      (fun time (_ : time ∈ (univ : Set ℝ)) => bound time) convex_univ (mem_univ second) (mem_univ first)

def correctedHalfDiagonalProfile (correction : ℝ → ℝ) (data : ℝ × (ℝ × ℝ)) : FourPointConfiguration :=
  Complex.exp (Complex.I * (((Real.sqrt 2 - 1) / 4 * shapeChartAngle data.2 + correction data.2.1 : ℝ) : ℂ)) •
    halfDiagonalCanonicalProfile data.1 data.2

theorem correctedHalfDiagonalProfile_contDiffAt_reference {correction : ℝ → ℝ}
    (smooth : ContDiffAt ℝ 1 correction 0) :
    ContDiffAt ℝ 1 (correctedHalfDiagonalProfile correction) (1, (0 : ℝ × ℝ)) := by
  have coordinate : ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) => data.2.1) (1, 0) :=
    contDiffAt_fst.comp (1, 0) contDiffAt_snd
  have phase : ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) =>
      (Real.sqrt 2 - 1) / 4 * shapeChartAngle data.2 + correction data.2.1) (1, 0) := by
    have angular : ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) => shapeChartAngle data.2) (1, 0) := by
      unfold shapeChartAngle
      fun_prop
    exact (contDiffAt_const.mul angular).add (smooth.comp (1, 0) coordinate)
  have complexPhase : ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) =>
      Complex.exp (Complex.I * (((Real.sqrt 2 - 1) / 4 * shapeChartAngle data.2 + correction data.2.1 : ℝ) : ℂ))) (1, 0) :=
    ((contDiffAt_const (c := Complex.I)).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (1, 0) phase)).cexp
  apply contDiffAt_pi.mpr
  intro patch
  exact complexPhase.mul (contDiffAt_pi.mp halfDiagonalCanonicalProfile_contDiffAt_reference patch)

theorem correctedHalfDiagonalProfile_exists_uniform_relative_bound {correction : ℝ → ℝ}
    (smooth : ContDiffAt ℝ 1 correction 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × (ℝ × ℝ),
      |first.1 - 1| + |first.2.1| + |first.2.2| < radius →
      |second.1 - 1| + |second.2.1| + |second.2.2| < radius →
      ∀ firstPhase secondPhase : ℝ,
      ‖Complex.exp (Complex.I * (firstPhase : ℂ)) • correctedHalfDiagonalProfile correction first -
        Complex.exp (Complex.I * (secondPhase : ℂ)) • correctedHalfDiagonalProfile correction second‖ ≤
      constant * (|first.1 - second.1| + |first.2.1 - second.2.1| +
        |first.2.2 - second.2.2| + |firstPhase - secondPhase|) := by
  let profile := correctedHalfDiagonalProfile correction
  let base : ℝ × (ℝ × ℝ) := (1, 0)
  obtain ⟨bound, region, regionMem, lipschitz⟩ :=
    (correctedHalfDiagonalProfile_contDiffAt_reference smooth).exists_lipschitzOnWith
  obtain ⟨baseRadius, basePositive, ballInside⟩ := Metric.mem_nhds_iff.mp regionMem
  let radius := min baseRadius 1
  let constant := (bound : ℝ) + ‖profile base‖ + 1
  have boundNonnegative := bound.coe_nonneg
  have baseNormNonnegative := norm_nonneg (profile base)
  refine ⟨radius, lt_min basePositive zero_lt_one, constant, by dsimp [constant]; linarith, ?_⟩
  intro first second firstSmall secondSmall firstPhase secondPhase
  have normDifference (first second : ℝ × (ℝ × ℝ)) :
      ‖first - second‖ ≤ |first.1 - second.1| + |first.2.1 - second.2.1| + |first.2.2 - second.2.2| := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg (first.2.1 - second.2.1), abs_nonneg (first.2.2 - second.2.2)])
      (max_le (by linarith [abs_nonneg (first.1 - second.1), abs_nonneg (first.2.2 - second.2.2)])
        (by linarith [abs_nonneg (first.1 - second.1), abs_nonneg (first.2.1 - second.2.1)]))
  have smallNorm (point : ℝ × (ℝ × ℝ))
      (small : |point.1 - 1| + |point.2.1| + |point.2.2| < radius) : ‖point - base‖ < radius := by
    have estimate : ‖point - base‖ ≤ |point.1 - 1| + |point.2.1| + |point.2.2| := by
      simpa only [base, Prod.fst, Prod.snd, Prod.fst_zero, Prod.snd_zero, sub_zero] using normDifference point base
    exact estimate.trans_lt small
  have nearby (point : ℝ × (ℝ × ℝ))
      (small : |point.1 - 1| + |point.2.1| + |point.2.2| < radius) : point ∈ region := by
    exact ballInside (by rw [Metric.mem_ball, dist_eq_norm]; exact (smallNorm point small).trans_le (min_le_left _ _))
  have baseInside : base ∈ region := ballInside (Metric.mem_ball_self basePositive)
  have profileDifference : ‖profile first - profile second‖ ≤
      (bound : ℝ) * (|first.1 - second.1| + |first.2.1 - second.2.1| + |first.2.2 - second.2.2|) := by
    have estimate : ‖profile first - profile second‖ ≤ (bound : ℝ) * ‖first - second‖ := by
      simpa only [dist_eq_norm] using lipschitz.dist_le_mul first (nearby first firstSmall)
        second (nearby second secondSmall)
    exact estimate.trans (mul_le_mul_of_nonneg_left (normDifference first second) boundNonnegative)
  have profileNorm : ‖profile second‖ ≤ constant := by
    have estimate := lipschitz.dist_le_mul second (nearby second secondSmall) base baseInside
    rw [dist_eq_norm, dist_eq_norm] at estimate
    have normSmall : ‖second - base‖ ≤ 1 := (smallNorm second secondSmall).le.trans (min_le_right _ _)
    have upper := estimate.trans (mul_le_mul_of_nonneg_left normSmall boundNonnegative)
    have triangle := norm_sub_le (profile second - profile base) (-profile base)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, mul_one] at triangle upper
    dsimp only [constant]
    linarith
  have identity : Complex.exp (Complex.I * (firstPhase : ℂ)) • profile first -
      Complex.exp (Complex.I * (secondPhase : ℂ)) • profile second =
      Complex.exp (Complex.I * (firstPhase : ℂ)) • (profile first - profile second) +
      (Complex.exp (Complex.I * (firstPhase : ℂ)) - Complex.exp (Complex.I * (secondPhase : ℂ))) • profile second := by
    funext patch
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul]
  have phaseNorm : ‖Complex.exp (Complex.I * (firstPhase : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self, Real.exp_zero]
  rw [phaseNorm, one_mul]
  have secondBound := mul_le_mul (complex_phase_exp_norm_sub_le firstPhase secondPhase) profileNorm
    (norm_nonneg _) (abs_nonneg _)
  dsimp only [constant] at profileNorm secondBound ⊢
  nlinarith [abs_nonneg (first.1 - second.1), abs_nonneg (first.2.1 - second.2.1),
    abs_nonneg (first.2.2 - second.2.2)]

end EulerNonuniqueness.Section6
