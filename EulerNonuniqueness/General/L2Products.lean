import EulerNonuniqueness.General.ConvolutionContinuity

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness

theorem integral_norm_mul_norm_le_eLpNorm_two {Domain First Second : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup First] [NormedAddCommGroup Second]
    {measure : Measure Domain} {first : Domain → First} {second : Domain → Second}
    (firstMember : MemLp first 2 measure) (secondMember : MemLp second 2 measure) :
    (∫ point, ‖first point‖ * ‖second point‖ ∂measure) ≤
      (eLpNorm first 2 measure).toReal * (eLpNorm second 2 measure).toReal := by
  have conjugacy : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have inequality := norm_integral_smul_le_eLpNorm conjugacy
    (show MemLp (fun point => ‖first point‖) (ENNReal.ofReal (2 : ℝ)) measure by simpa using firstMember.norm)
    (show MemLp (fun point => ‖second point‖) (ENNReal.ofReal (2 : ℝ)) measure by simpa using secondMember.norm)
  have absoluteBound : |∫ point, ‖first point‖ * ‖second point‖ ∂measure| ≤
      (eLpNorm first 2 measure).toReal * (eLpNorm second 2 measure).toReal := by
    simpa only [smul_eq_mul, Real.norm_eq_abs, ENNReal.ofReal_ofNat, eLpNorm_norm] using inequality
  exact (le_abs_self _).trans absoluteBound

end EulerNonuniqueness
