import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Set Filter
open scoped Topology

namespace MeasureTheory

theorem tendsto_integral_norm_indicator_sub_of_persistence_of_area_tendsto
    {domainType parameter : Type*} [MeasurableSpace domainType] [TopologicalSpace parameter]
    [FirstCountableTopology parameter] (measure : Measure domainType)
    (domain : parameter → Set domainType) (base : parameter)
    (measurable : ∀ point, MeasurableSet (domain point))
    (finite : ∀ point, measure (domain point) ≠ ⊤)
    (persistence : ∀ position ∈ domain base, ∀ᶠ point in 𝓝 base, position ∈ domain point)
    (areaConvergence : Tendsto (fun point => measure.real (domain point)) (𝓝 base) (𝓝 (measure.real (domain base)))) :
    Tendsto (fun point => ∫ position,
      ‖(domain point).indicator (fun _ => (1 : ℝ)) position -
        (domain base).indicator (fun _ => (1 : ℝ)) position‖ ∂measure) (𝓝 base) (𝓝 0) := by
  let indicator : parameter → domainType → ℝ := fun point => (domain point).indicator (fun _ => (1 : ℝ))
  let intersection : parameter → domainType → ℝ := fun point position => indicator point position * indicator base position
  have indicatorIntegrable (point : parameter) : Integrable (indicator point) measure :=
    (integrable_indicator_iff (measurable point)).mpr (integrableOn_const.mpr (Or.inr (lt_top_iff_ne_top.mpr (finite point))))
  have indicatorIntegral (point : parameter) : (∫ position, indicator point position ∂measure) = measure.real (domain point) := by
    dsimp only [indicator]
    rw [integral_indicator (measurable point), setIntegral_const]
    simp only [smul_eq_mul, mul_one, Measure.real]
  have intersectionBound (point : parameter) (position : domainType) : ‖intersection point position‖ ≤ indicator base position := by
    dsimp only [intersection, indicator]
    by_cases first : position ∈ domain point <;> by_cases second : position ∈ domain base <;> simp [first, second]
  have intersectionMeasurable (point : parameter) : AEStronglyMeasurable (intersection point) measure :=
    (indicatorIntegrable point).aestronglyMeasurable.mul (indicatorIntegrable base).aestronglyMeasurable
  have intersectionIntegrable (point : parameter) : Integrable (intersection point) measure :=
    (indicatorIntegrable base).mono' (intersectionMeasurable point) (Eventually.of_forall (intersectionBound point))
  have intersectionConvergence : Tendsto (fun point => ∫ position, intersection point position ∂measure)
      (𝓝 base) (𝓝 (measure.real (domain base))) := by
    rw [← indicatorIntegral base]
    apply tendsto_integral_filter_of_dominated_convergence (indicator base)
    · exact Eventually.of_forall intersectionMeasurable
    · exact Eventually.of_forall fun point => Eventually.of_forall (intersectionBound point)
    · exact indicatorIntegrable base
    · exact Eventually.of_forall fun position => by
        by_cases inside : position ∈ domain base
        · apply tendsto_const_nhds.congr'
          filter_upwards [persistence position inside] with point membership
          simp [intersection, indicator, inside, membership]
        · have identity : (fun point => intersection point position) = fun _ => indicator base position := by
            funext point
            simp [intersection, indicator, inside]
          rw [identity]
          exact tendsto_const_nhds
  have normIntegral (point : parameter) :
      (∫ position, ‖indicator point position - indicator base position‖ ∂measure) =
      measure.real (domain point) + measure.real (domain base) -
        2 * ∫ position, intersection point position ∂measure := by
    have identity : (fun position => ‖indicator point position - indicator base position‖) =
        (fun position => indicator point position + indicator base position - 2 * intersection point position) := by
      funext position
      dsimp only [intersection, indicator]
      by_cases first : position ∈ domain point <;> by_cases second : position ∈ domain base <;> norm_num [first, second]
    have sumIntegrable : Integrable (fun position => indicator point position + indicator base position) measure :=
      (indicatorIntegrable point).add (indicatorIntegrable base)
    rw [identity, integral_sub sumIntegrable
      ((intersectionIntegrable point).const_mul 2), integral_add (indicatorIntegrable point) (indicatorIntegrable base),
      integral_const_mul, indicatorIntegral point, indicatorIntegral base]
  have convergence : Tendsto (fun point => measure.real (domain point) + measure.real (domain base) -
      2 * ∫ position, intersection point position ∂measure) (𝓝 base)
      (𝓝 (measure.real (domain base) + measure.real (domain base) - 2 * measure.real (domain base))) :=
    (areaConvergence.add tendsto_const_nhds).sub (intersectionConvergence.const_mul 2)
  have zero : measure.real (domain base) + measure.real (domain base) - 2 * measure.real (domain base) = 0 := by ring
  rw [zero] at convergence
  change Tendsto (fun point => ∫ position, ‖indicator point position - indicator base position‖ ∂measure) (𝓝 base) (𝓝 0)
  simpa only [normIntegral] using convergence

end MeasureTheory
