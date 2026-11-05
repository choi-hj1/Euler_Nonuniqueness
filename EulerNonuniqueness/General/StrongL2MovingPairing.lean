import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace MeasureTheory

theorem tendsto_integral_mul_of_strongL2_strongL2
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} {first second : Index → Domain → ℝ} {firstLimit secondLimit : Domain → ℝ}
    (firstMembers : ∀ index, MemLp (first index) 2 measure)
    (secondMembers : ∀ index, MemLp (second index) 2 measure)
    (firstLimitMember : MemLp firstLimit 2 measure) (secondLimitMember : MemLp secondLimit 2 measure)
    (firstConverges : Tendsto (fun index => eLpNorm (first index - firstLimit) 2 measure) filter (𝓝 0))
    (secondConverges : Tendsto (fun index => eLpNorm (second index - secondLimit) 2 measure) filter (𝓝 0)) :
    Tendsto (fun index => ∫ position, first index position * second index position ∂measure)
      filter (𝓝 (∫ position, firstLimit position * secondLimit position ∂measure)) := by
  have firstQuotient := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' first firstMembers firstLimit firstLimitMember).mpr firstConverges
  have secondQuotient := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' second secondMembers secondLimit secondLimitMember).mpr secondConverges
  have paired : Tendsto
      (fun index => ⟪(firstMembers index).toLp (first index), (secondMembers index).toLp (second index)⟫_ℝ)
      filter (𝓝 ⟪firstLimitMember.toLp firstLimit, secondLimitMember.toLp secondLimit⟫_ℝ) :=
    firstQuotient.inner secondQuotient
  simpa only [inner_toLp_eq_integral_mul] using paired

end MeasureTheory
