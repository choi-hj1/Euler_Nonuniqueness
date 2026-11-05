import EulerNonuniqueness.Section3.ExtendedCrossContour

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance crossUniformHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance crossUniformC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem crossContourPhaseIntegrand_uniform_norm_bound
    (target source : PeriodicC1HolderHalf) {lower bound : ℝ}
    (positive : 0 < lower)
    (separated : ∀ sourceLabel targetLabel, lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖)
    (targetBound : ‖target‖ ≤ bound) (sourceBound : ‖source‖ ≤ bound) (label : ℝ) :
    ‖crossContourPhaseIntegrand target source positive separated label‖ ≤
      8 * crossContourPhaseBound bound lower * bound := by
  have nonnegative : 0 ≤ bound := (norm_nonneg target).trans targetBound
  have phaseBound : ‖c1Phase (crossContourDifference target (source.val.1 label)) positive (separated label)‖ ≤
      crossContourPhaseBound bound lower := by
    have differenceBound : ‖crossContourDifference target (source.val.1 label)‖ ≤ 2 * bound :=
      (crossContourDifference_norm_bound target source label).trans (by linarith)
    have estimate := c1Phase_uniform_norm_bound (crossContourDifference target (source.val.1 label))
      positive (separated label) differenceBound
    apply estimate.trans_eq
    unfold crossContourPhaseBound
    ring
  have tangentBound : ‖c1Constant (star (source.val.2.val.1 label))‖ ≤ bound := by
    exact (c1Constant_norm_bound _).trans (by
      rw [norm_star]
      exact (PeriodicC1HolderHalf.speed_bound source label).trans sourceBound)
  have phaseNonnegative : 0 ≤ crossContourPhaseBound bound lower := (norm_nonneg _).trans phaseBound
  exact (c1Product_norm_bound _ _).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left phaseBound (by norm_num)) tangentBound
      (norm_nonneg _) (by positivity))

theorem extendedCrossContourVelocity_uniform_norm_bound
    (target source : PeriodicC1HolderHalf) {lower bound : ℝ}
    (positive : 0 < lower)
    (separated : ∀ sourceLabel targetLabel, lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖)
    (targetBound : ‖target‖ ≤ bound) (sourceBound : ‖source‖ ≤ bound) :
    ‖extendedCrossContourVelocity target source‖ ≤ 4 * crossContourPhaseBound bound lower * bound := by
  rw [extendedCrossContourVelocity_eq target source positive separated, crossContourVelocityBanach,
    norm_smul (1 / (4 * Real.pi) : ℝ)
      (∫ label in (-Real.pi)..Real.pi, crossContourPhaseIntegrand target source positive separated label), Real.norm_eq_abs,
    abs_of_pos (show 0 < 1 / (4 * Real.pi) by positivity)]
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi)
    (fun label _ => crossContourPhaseIntegrand_uniform_norm_bound target source positive separated targetBound sourceBound label)
  apply (mul_le_mul_of_nonneg_left integralBound (by positivity)).trans_eq
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
  field_simp
  ring

end EulerNonuniqueness.Paper
