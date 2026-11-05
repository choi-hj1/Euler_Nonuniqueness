import EulerNonuniqueness.Section3.DiskAreaMeanConstraint
import EulerNonuniqueness.Section3.DiskContourGenerator

namespace EulerNonuniqueness.Paper

open MeasureTheory

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance areaProjectionHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance areaProjectionC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskRadialPart_value (direction : PeriodicC1HolderHalf) (label : ℝ) :
    (diskRadialPart direction).val.1 label = ((star (standardCircle label) * direction.val.1 label).re : ℂ) := by
  change (1 / 2 : ℝ) • (star (standardCircle label) * direction.val.1 label +
    star (star (standardCircle label) * direction.val.1 label)) = _
  apply Complex.ext <;>
    simp only [Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem periodicMeanProjection_diskRadialPart (direction : PeriodicC1HolderHalf) :
    periodicMeanProjectionCCLM (diskRadialPart direction) = c1Constant (diskRadialMean direction : ℂ) := by
  rw [periodicMeanProjectionCCLM_eq_constant]
  congr 1
  have shifted := (PeriodicC1HolderHalf.periodic (diskRadialPart direction)).intervalIntegral_add_eq (-Real.pi) 0
  have window : (∫ label in (-Real.pi)..Real.pi, (diskRadialPart direction).val.1 label) =
      ∫ label in (0 : ℝ)..(2 * Real.pi), (diskRadialPart direction).val.1 label := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] using shifted
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ label in (0 : ℝ)..(2 * Real.pi), (diskRadialPart direction).val.1 label) = _
  rw [← window]
  simp_rw [diskRadialPart_value]
  rw [intervalIntegral.integral_ofReal]
  exact (Complex.ofReal_mul _ _).symm

theorem periodicMeanProjection_diskRadialPart_norm_le_of_area
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (area : (volume (nearCircleInterior data small)).toReal = Real.pi) :
    ‖periodicMeanProjectionCCLM (diskRadialPart (data - standardCircleBanach))‖ ≤
      (1 / 2 : ℝ) * ‖data - standardCircleBanach‖ ^ 2 := by
  rw [periodicMeanProjection_diskRadialPart]
  exact (c1Constant_norm_bound _).trans (by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using diskRadialMean_abs_le_of_domain_area data small area)

end

end EulerNonuniqueness.Paper
