import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace MeasureTheory

theorem ae_eq_of_weakL2_limits_of_smooth_pairing_sub_tendsto_zero
    {Domain Index : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [FiniteDimensional ℝ Domain] [MeasurableSpace Domain] [BorelSpace Domain]
    {measure : Measure Domain} [IsLocallyFiniteMeasure measure]
    {filter : Filter Index} [filter.NeBot] {first second : Index → Domain → ℝ}
    {firstLimit secondLimit : Domain → ℝ}
    (firstMember : MemLp firstLimit 2 measure) (secondMember : MemLp secondLimit 2 measure)
    (firstWeak : ∀ test : Domain → ℝ, MemLp test 2 measure →
      Tendsto (fun index => ∫ point, first index point * test point ∂measure)
        filter (𝓝 (∫ point, firstLimit point * test point ∂measure)))
    (secondWeak : ∀ test : Domain → ℝ, MemLp test 2 measure →
      Tendsto (fun index => ∫ point, second index point * test point ∂measure)
        filter (𝓝 (∫ point, secondLimit point * test point ∂measure)))
    (close : ∀ test : Domain → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      Tendsto (fun index => (∫ point, first index point * test point ∂measure) -
        (∫ point, second index point * test point ∂measure)) filter (𝓝 0)) :
    firstLimit =ᵐ[measure] secondLimit := by
  apply ae_eq_of_integral_contDiff_smul_eq (firstMember.locallyIntegrable (by norm_num))
    (secondMember.locallyIntegrable (by norm_num))
  intro test smooth compact
  have testMember : MemLp test 2 measure := smooth.continuous.memLp_of_hasCompactSupport compact
  have difference := (firstWeak test testMember).sub (secondWeak test testMember)
  have equality := sub_eq_zero.mp (tendsto_nhds_unique difference (close test smooth compact))
  simpa only [smul_eq_mul, mul_comm] using equality

end MeasureTheory
