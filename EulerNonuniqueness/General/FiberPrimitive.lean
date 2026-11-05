import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

def fiberPrimitive {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (coefficient : ℝ × ℝ → Value) (graph : ℝ → ℝ) (point : ℝ × ℝ) : Value :=
  ∫ parameter in (0 : ℝ)..1, coefficient (point.1, graph point.1 + parameter * point.2)

theorem fiber_primitive_identity {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    {error coefficient : ℝ × ℝ → Value} {graph : ℝ → ℝ} (point : ℝ × ℝ)
    (vanishing : error (point.1, graph point.1) = 0)
    (continuous : ContinuousOn (fun parameter => coefficient (point.1, graph point.1 + parameter * point.2)) (Icc 0 1))
    (equation : ∀ parameter ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun stable => error (point.1, stable)) (coefficient (point.1, graph point.1 + parameter * point.2))
        (graph point.1 + parameter * point.2)) :
    error (point.1, graph point.1 + point.2) = point.2 • fiberPrimitive coefficient graph point := by
  have derivative (parameter : ℝ) (member : parameter ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun current => error (point.1, graph point.1 + current * point.2))
        (point.2 • coefficient (point.1, graph point.1 + parameter * point.2)) parameter := by
    have affine : HasDerivAt (fun current : ℝ => graph point.1 + current * point.2) point.2 parameter := by
      simpa only [id_eq, one_mul] using (((hasDerivAt_id parameter).mul_const point.2).const_add (graph point.1))
    have composed := (equation parameter member).scomp parameter affine
    simpa only [id_eq, one_mul, add_comm] using composed
  have continuousInterval : ContinuousOn (fun parameter => coefficient (point.1, graph point.1 + parameter * point.2)) (uIcc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using continuous
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun parameter member => derivative parameter (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ member))
    (continuousInterval.const_smul point.2).intervalIntegrable
  simpa only [fiberPrimitive, intervalIntegral.integral_smul, mul_one, mul_zero, one_mul, zero_mul, add_zero, vanishing, sub_zero] using actual.symm

end EulerNonuniqueness
