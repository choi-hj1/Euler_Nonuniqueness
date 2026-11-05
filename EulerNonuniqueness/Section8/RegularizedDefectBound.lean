import EulerNonuniqueness.Section8.RegularizedApproximation
import EulerNonuniqueness.Section8.RegularizedVelocityConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

def regularizedDefectBound (source : Vorticity) (index : ℕ) : ℝ :=
  (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal *
    (eLpNorm (nearRegularizedKernelDifference (regularizationScale index))
      (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
        (∫ label, ‖source label‖) * (regularizationScale index ^ 2 / (2 * Real.pi))

theorem regularizedDefectBound_nonnegative (source : Vorticity) (index : ℕ) :
    0 ≤ regularizedDefectBound source index := by
  dsimp [regularizedDefectBound]
  positivity

theorem tendsto_regularizedDefectBound (source : Vorticity) :
    Tendsto (regularizedDefectBound source) atTop (𝓝 0) := by
  have nearConvergence := tendsto_eLpNorm_nearRegularizedKernelDifference
    regularizationScale_positive tendsto_regularizationScale
    (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)
  have nearReal : Tendsto (fun index =>
      (eLpNorm (nearRegularizedKernelDifference (regularizationScale index))
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp nearConvergence
  have farReal : Tendsto (fun index => regularizationScale index ^ 2 / (2 * Real.pi)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using
      (tendsto_regularizationScale.pow 2).div_const (2 * Real.pi)
  simpa only [regularizedDefectBound, mul_zero, zero_add] using
    (nearReal.const_mul (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal).add
      (farReal.const_mul (∫ label, ‖source label‖))

theorem norm_regularizedApproximation_velocity_defect_le {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (index : ℕ) {time : ℝ} (inside : time ∈ Icc 0 horizon) (position : Plane) :
    ‖regularizedBiotSavart (regularizationScale index)
        (regularizedApproximation integrable nonnegative index time) position -
      biotSavart (regularizedApproximation integrable nonnegative index time) position‖ ≤
        regularizedDefectBound source index := by
  let flow := regularizedApproximationFlow integrable nonnegative index
  have estimate := norm_regularizedBiotSavart_sub_le (regularizationScale_positive index)
    (flow.integrable_vorticity nonnegative inside) (flow.memLp_vorticity nonnegative inside membership) position
  simpa only [flow.eLpNorm_vorticity nonnegative inside, flow.integral_norm_vorticity nonnegative inside,
    regularizedDefectBound] using estimate

end EulerNonuniqueness
