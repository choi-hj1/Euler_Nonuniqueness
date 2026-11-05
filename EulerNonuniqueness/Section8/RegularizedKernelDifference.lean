import EulerNonuniqueness.Section8.RegularizedKernelConvergence
import EulerNonuniqueness.Section8.Compactness

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

theorem regularizedBiotSavartKernel_sub_kernel {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    regularizedBiotSavartKernel scale position - biotSavartKernel position =
      -(scale ^ 2 / (‖position‖ ^ 2 + scale ^ 2)) • biotSavartKernel position := by
  by_cases zero : position = 0
  · simp [zero, regularizedBiotSavartKernel_zero, biotSavartKernel]
  have radiusNonzero : (‖position‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr zero)
  have totalNonzero : ((‖position‖ ^ 2 + scale ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold regularizedBiotSavartKernel biotSavartKernel
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_add] at *
  field_simp
  ring

theorem norm_regularizedBiotSavartKernel_sub_le {scale : ℝ} (positive : 0 < scale)
    {position : Plane} (nonzero : position ≠ 0) :
    ‖regularizedBiotSavartKernel scale position - biotSavartKernel position‖ ≤
      scale ^ 2 / (2 * Real.pi * ‖position‖ ^ 3) := by
  have radiusPositive := norm_pos_iff.mpr nonzero
  have totalPositive : 0 < ‖position‖ ^ 2 + scale ^ 2 := by positivity
  rw [regularizedBiotSavartKernel_sub_kernel positive, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg scale) totalPositive.le),
    norm_biotSavartKernel]
  calc
    _ ≤ scale ^ 2 / ‖position‖ ^ 2 * (1 / (2 * Real.pi * ‖position‖)) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (sq_nonneg scale) (by positivity)
          (by nlinarith [sq_nonneg scale])) (by positivity)
    _ = _ := by field_simp; ring

theorem norm_regularizedBiotSavartKernel_sub_le_far {scale : ℝ} (positive : 0 < scale)
    {position : Plane} (far : 1 ≤ ‖position‖) :
    ‖regularizedBiotSavartKernel scale position - biotSavartKernel position‖ ≤ scale ^ 2 / (2 * Real.pi) := by
  have nonzero : position ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le far)
  calc
    _ ≤ scale ^ 2 / (2 * Real.pi * ‖position‖ ^ 3) := norm_regularizedBiotSavartKernel_sub_le positive nonzero
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg scale) (by positivity)
      (by nlinarith [one_le_pow₀ far (n := 3), Real.pi_pos])

theorem regularizedKernel_sub_memLp_ball {scale exponent radius : ℝ} (positive : 0 < scale)
    (exponentPositive : 0 < exponent) (exponentBound : exponent < 2) (radiusPositive : 0 < radius) :
    MemLp (regularizedBiotSavartKernel scale - biotSavartKernel) (ENNReal.ofReal exponent)
      (volume.restrict (Metric.ball (0 : Plane) radius)) := by
  have kernelMember := memLp_biotSavartKernel_ball exponentPositive exponentBound radiusPositive
  have regularizedMember : MemLp (regularizedBiotSavartKernel scale) (ENNReal.ofReal exponent)
      (volume.restrict (Metric.ball (0 : Plane) radius)) :=
    kernelMember.mono (contDiff_regularizedBiotSavartKernel positive).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_regularizedBiotSavartKernel_le_kernel positive))
  exact regularizedMember.sub kernelMember

theorem tendsto_eLpNorm_regularizedKernel_sub_ball {scales : ℕ → ℝ}
    (positive : ∀ index, 0 < scales index) (convergence : Tendsto scales atTop (𝓝 0))
    {exponent radius : ℝ} (exponentPositive : 0 < exponent) (exponentBound : exponent < 2)
    (radiusPositive : 0 < radius) :
    Tendsto (fun index => eLpNorm (regularizedBiotSavartKernel (scales index) - biotSavartKernel)
      (ENNReal.ofReal exponent) (volume.restrict (Metric.ball (0 : Plane) radius))) atTop (𝓝 0) :=
  tendsto_eLpNorm_regularizedKernel_sub positive convergence
    (ENNReal.ofReal_pos.mpr exponentPositive) ENNReal.ofReal_ne_top
    (memLp_biotSavartKernel_ball exponentPositive exponentBound radiusPositive)

end EulerNonuniqueness
