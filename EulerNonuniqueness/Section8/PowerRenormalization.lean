import EulerNonuniqueness.Section8.RenormalizedMassConservation
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def powerCutoffBump (index : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(index : ℝ) + 1, (index : ℝ) + 2, by positivity, by linarith⟩

def powerRenormalization (exponent : ℝ) (index : ℕ) (value : ℝ) : ℝ :=
  powerCutoffBump index value * ‖value‖ ^ exponent

theorem powerRenormalization_admissible {exponent : ℝ} (bound : 1 < exponent) (index : ℕ) :
    AdmissibleRenormalization (powerRenormalization exponent index) := by
  have smooth : ContDiff ℝ 1 (powerRenormalization exponent index) :=
    (powerCutoffBump index).contDiff.mul (contDiff_norm_rpow bound)
  have compact : HasCompactSupport (powerRenormalization exponent index) :=
    (powerCutoffBump index).hasCompactSupport.mul_right
  obtain ⟨derivativeBound, bounded⟩ := compact.deriv.exists_bound_of_continuous (smooth.continuous_deriv le_rfl)
  refine ⟨smooth, max derivativeBound 0, le_max_right _ _, fun value => ?_⟩
  have estimate : |deriv (powerRenormalization exponent index) value| ≤ derivativeBound := by
    simpa only [Real.norm_eq_abs] using bounded value
  exact estimate.trans (le_max_left _ _)

theorem powerRenormalization_zero {exponent : ℝ} (positive : 0 < exponent) (index : ℕ) :
    powerRenormalization exponent index 0 = 0 := by
  simp [powerRenormalization, Real.zero_rpow positive.ne']

theorem powerRenormalization_norm_le (exponent : ℝ) (index : ℕ) (value : ℝ) :
    ‖powerRenormalization exponent index value‖ ≤ ‖value‖ ^ exponent := by
  rw [powerRenormalization, norm_mul, Real.norm_eq_abs, abs_of_nonneg (powerCutoffBump index).nonneg,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _) (powerCutoffBump index).le_one

theorem tendsto_powerRenormalization (exponent : ℝ) (value : ℝ) :
    Tendsto (fun index => powerRenormalization exponent index value) atTop (𝓝 (‖value‖ ^ exponent)) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨threshold, bound⟩ := exists_nat_gt ‖value‖
  filter_upwards [eventually_ge_atTop threshold] with index indexBound
  have inside : value ∈ Metric.closedBall (0 : ℝ) (powerCutoffBump index).rIn := by
    change dist value 0 ≤ (index : ℝ) + 1
    simp only [dist_zero_right]
    exact (le_of_lt bound).trans (by exact_mod_cast Nat.le_trans indexBound (Nat.le_add_right index 1))
  simp only [powerRenormalization, (powerCutoffBump index).one_of_mem_closedBall inside, one_mul]

end EulerNonuniqueness
