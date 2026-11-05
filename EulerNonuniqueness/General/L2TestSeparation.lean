import EulerNonuniqueness.General.L2PairingContinuity
import EulerNonuniqueness.General.WeakSupport

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem ae_eq_of_memLp_two_of_integral_mul_eq
    {Domain : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {first second : Domain → ℝ} (firstMember : MemLp first 2 measure)
    (secondMember : MemLp second 2 measure)
    (equal : ∀ test : Domain → ℝ, MemLp test 2 measure →
      (∫ point, first point * test point ∂measure) = ∫ point, second point * test point ∂measure) :
    first =ᵐ[measure] second := by
  have differenceMember := firstMember.sub secondMember
  have firstProduct : Integrable (fun point => first point * (first point - second point)) measure :=
    firstMember.integrable_mul differenceMember
  have secondProduct : Integrable (fun point => second point * (first point - second point)) measure :=
    secondMember.integrable_mul differenceMember
  have pairing := equal (first - second) differenceMember
  have squareIntegral : (∫ point, (first point - second point) ^ 2 ∂measure) = 0 := by
    calc
      _ = ∫ point, first point * (first point - second point) -
          second point * (first point - second point) ∂measure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun point => by ring
      _ = _ := by rw [integral_sub firstProduct secondProduct]; exact sub_eq_zero.mpr pairing
  have zero := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun point => sq_nonneg (first point - second point)) differenceMember.integrable_sq).mp
      squareIntegral
  exact zero.mono fun point equality => sub_eq_zero.mp (sq_eq_zero_iff.mp equality)

theorem ae_eq_indicator_of_weakL2_tendsto_of_support
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} [filter.NeBot] {sequence : Index → Domain → ℝ} {limit : Domain → ℝ}
    {region : Set Domain} (measurable : MeasurableSet region)
    (limitMember : MemLp limit 2 measure)
    (supported : ∀ index, Function.support (sequence index) ⊆ region)
    (weak : ∀ test : Domain → ℝ, MemLp test 2 measure →
      Tendsto (fun index => ∫ point, sequence index point * test point ∂measure)
        filter (𝓝 (∫ point, limit point * test point ∂measure))) :
    limit =ᵐ[measure] region.indicator limit := by
  apply ae_eq_of_memLp_two_of_integral_mul_eq limitMember (limitMember.indicator measurable)
  intro test testMember
  exact tendsto_nhds_unique (weak test testMember)
    (tendsto_integral_mul_indicator_limit_of_support measurable supported weak testMember)

end MeasureTheory
