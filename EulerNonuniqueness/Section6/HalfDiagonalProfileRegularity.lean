import EulerNonuniqueness.Section6.HalfDiagonalConfigurationMatching
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem halfDiagonalRatioFromShape_contDiffAt_zero :
    ContDiffAt ℝ 1 halfDiagonalRatioFromShape (0 : ℝ × ℝ) := by
  have radial : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => rhombusRatio * (1 + point.1 + point.2)) 0 := by
    fun_prop
  have root := radial.sqrt (by simpa using reference_rhombusRatio_bounds.1.ne')
  have complexRoot : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ => (Real.sqrt (rhombusRatio * (1 + point.1 + point.2)) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 root
  have angular : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ => Complex.exp ((((Real.pi + Real.sqrt 2 * (point.1 - point.2)) / 2 : ℝ) : ℂ) * Complex.I)) 0 := by
    have argument : ContDiffAt ℝ 1 (fun point : ℝ × ℝ =>
        (((Real.pi + Real.sqrt 2 * (point.1 - point.2)) / 2 : ℝ) : ℂ) * Complex.I) 0 := by
      have realArgument : ContDiffAt ℝ 1 (fun point : ℝ × ℝ =>
          (Real.pi + Real.sqrt 2 * (point.1 - point.2)) / 2) 0 :=
        (contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_fst.sub contDiffAt_snd))).div_const 2
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realArgument).mul contDiffAt_const
    exact argument.cexp
  exact complexRoot.mul angular

theorem halfDiagonalRatioFromShape_norm_sq_zero :
    ‖halfDiagonalRatioFromShape (0 : ℝ × ℝ)‖ ^ 2 = rhombusRatio := by
  simp only [halfDiagonalRatioFromShape, Prod.fst_zero, Prod.snd_zero, add_zero, sub_zero,
    mul_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  norm_num
  exact Real.sq_sqrt reference_rhombusRatio_bounds.1.le

theorem halfDiagonalCanonicalProfile_contDiffAt_reference :
    ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) => halfDiagonalCanonicalProfile data.1 data.2) (1, 0) := by
  have ratio : ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) => halfDiagonalRatioFromShape data.2) (1, 0) :=
    halfDiagonalRatioFromShape_contDiffAt_zero.comp (1, 0) contDiffAt_snd
  have denominator : ContDiffAt ℝ 1 (fun data : ℝ × (ℝ × ℝ) =>
      1 - ‖halfDiagonalRatioFromShape data.2‖ ^ 2) (1, 0) :=
    contDiffAt_const.sub (ratio.norm_sq (𝕜 := ℂ))
  have denominatorPositive : 0 < 1 - ‖halfDiagonalRatioFromShape (0 : ℝ × ℝ)‖ ^ 2 := by
    rw [halfDiagonalRatioFromShape_norm_sq_zero]
    linarith [reference_rhombusRatio_bounds.2]
  have quotient := contDiffAt_fst.div denominator denominatorPositive.ne'
  have amplitude := quotient.sqrt (by change (1 : ℝ) / (1 - ‖halfDiagonalRatioFromShape (0 : ℝ × ℝ)‖ ^ 2) ≠ 0; positivity)
  have complexAmplitude := Complex.ofRealCLM.contDiff.contDiffAt.comp (1, 0) amplitude
  apply contDiffAt_pi.mpr
  intro patch
  fin_cases patch
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using complexAmplitude
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using complexAmplitude.neg
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using complexAmplitude.mul ratio
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using (complexAmplitude.mul ratio).neg

theorem halfDiagonalCanonicalProfile_exists_uniform_lipschitz :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × (ℝ × ℝ),
      |first.1 - 1| + |first.2.1| + |first.2.2| < radius →
      |second.1 - 1| + |second.2.1| + |second.2.2| < radius →
      ‖halfDiagonalCanonicalProfile first.1 first.2 - halfDiagonalCanonicalProfile second.1 second.2‖ ≤
        constant * (|first.1 - second.1| + |first.2.1 - second.2.1| + |first.2.2 - second.2.2|) := by
  obtain ⟨bound, region, regionMem, lipschitz⟩ := halfDiagonalCanonicalProfile_contDiffAt_reference.exists_lipschitzOnWith
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp regionMem
  refine ⟨radius, radiusPositive, (bound : ℝ) + 1, by have := bound.coe_nonneg; linarith, ?_⟩
  intro first second firstSmall secondSmall
  have nearby (point : ℝ × (ℝ × ℝ))
      (small : |point.1 - 1| + |point.2.1| + |point.2.2| < radius) : point ∈ region := by
    apply ballInside
    rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, Real.norm_eq_abs]
    exact (max_le (by linarith [abs_nonneg point.2.1, abs_nonneg point.2.2])
      (max_le (by linarith [abs_nonneg (point.1 - 1), abs_nonneg point.2.2])
        (by linarith [abs_nonneg (point.1 - 1), abs_nonneg point.2.1]))).trans_lt small
  have estimate := lipschitz.dist_le_mul first (nearby first firstSmall) second (nearby second secondSmall)
  rw [dist_eq_norm, dist_eq_norm] at estimate
  have normBound : ‖first - second‖ ≤ |first.1 - second.1| + |first.2.1 - second.2.1| + |first.2.2 - second.2.2| := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg (first.2.1 - second.2.1), abs_nonneg (first.2.2 - second.2.2)])
      (max_le (by linarith [abs_nonneg (first.1 - second.1), abs_nonneg (first.2.2 - second.2.2)])
        (by linarith [abs_nonneg (first.1 - second.1), abs_nonneg (first.2.1 - second.2.1)]))
  exact estimate.trans ((mul_le_mul_of_nonneg_left normBound bound.coe_nonneg).trans
    (mul_le_mul_of_nonneg_right (by linarith : (bound : ℝ) ≤ (bound : ℝ) + 1) (by positivity)))

end EulerNonuniqueness.Section6
