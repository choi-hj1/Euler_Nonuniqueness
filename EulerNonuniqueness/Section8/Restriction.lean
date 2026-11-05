import EulerNonuniqueness.Definitions

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness

theorem ScalarTestOn.mono {smaller horizon : ℝ} {test : ℝ × Plane → ℝ}
    (admissible : ScalarTestOn smaller test) (ordered : smaller ≤ horizon) :
    ScalarTestOn horizon test :=
  ⟨admissible.1, admissible.2.1,
    fun time position after => admissible.2.2 time position (ordered.trans after)⟩

theorem VectorTestOn.mono {smaller horizon : ℝ} {test : ℝ × Plane → Plane}
    (admissible : VectorTestOn smaller test) (ordered : smaller ≤ horizon) :
    VectorTestOn horizon test :=
  ⟨admissible.1, admissible.2.1,
    fun time position after => admissible.2.2.1 time position (ordered.trans after),
    admissible.2.2.2⟩

theorem fderiv_eq_zero_after_horizon {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {horizon : ℝ} {test : ℝ × Plane → Value}
    (vanishes : ∀ time position, horizon ≤ time → test (time, position) = 0)
    {point : ℝ × Plane} (after : horizon < point.1) :
    fderiv ℝ test point = 0 := by
  have equalNear : test =ᶠ[𝓝 point] fun _ => 0 := by
    filter_upwards [continuous_fst.continuousAt.eventually (eventually_gt_nhds after)]
      with nearby later
    exact vanishes nearby.1 nearby.2 later.le
  rw [equalNear.fderiv_eq, fderiv_const_apply]

theorem spacetimeMeasure_mono {smaller horizon : ℝ} (ordered : smaller ≤ horizon) :
    spacetimeMeasure smaller ≤ spacetimeMeasure horizon := by
  simp only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ]
  apply Measure.restrict_mono _ le_rfl
  exact Set.prod_mono (Ioo_subset_Ioo_right ordered) Subset.rfl

theorem integral_spacetime_eq_of_vanishes_after {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] {smaller horizon : ℝ}
    {integrand : ℝ × Plane → Value} (ordered : smaller ≤ horizon)
    (vanishes : ∀ point, smaller < point.1 → integrand point = 0) :
    (∫ point, integrand point ∂spacetimeMeasure horizon) =
      ∫ point, integrand point ∂spacetimeMeasure smaller := by
  simp only [spacetimeMeasure, Measure.restrict_prod_eq_prod_univ]
  apply setIntegral_eq_of_subset_of_ae_diff_eq_zero
    (measurableSet_Ioo.prod MeasurableSet.univ).nullMeasurableSet
    (Set.prod_mono (Ioo_subset_Ioo_right ordered) Subset.rfl)
  have notBoundary : ∀ᵐ point ∂((volume : Measure ℝ).prod (volume : Measure Plane)),
      point.1 ≠ smaller := Measure.quasiMeasurePreserving_fst.ae
        (show ∀ᵐ time ∂(volume : Measure ℝ), time ≠ smaller from by
          simp only [ae_iff, not_not, Set.setOf_eq_eq_singleton, measure_singleton])
  filter_upwards [notBoundary] with point different inside
  apply vanishes point
  have atLeast : smaller ≤ point.1 := by
    by_contra earlier
    exact inside.2 ⟨⟨inside.1.1.1, lt_of_not_ge earlier⟩, mem_univ _⟩
  exact lt_of_le_of_ne atLeast different.symm

theorem WeakTransportOn.mono {smaller horizon : ℝ} {initial : Vorticity}
    {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity)
    (ordered : smaller ≤ horizon) : WeakTransportOn smaller initial omega velocity := by
  intro test admissible
  obtain ⟨integrable, initialIntegrable, identity⟩ := transport test (admissible.mono ordered)
  refine ⟨integrable.mono_measure (spacetimeMeasure_mono ordered), initialIntegrable, ?_⟩
  rw [integral_spacetime_eq_of_vanishes_after ordered] at identity
  · exact identity
  · intro point after
    simp only [timeDerivative, spatialDerivative,
      fderiv_eq_zero_after_horizon admissible.2.2 after,
      ContinuousLinearMap.zero_apply, add_zero, mul_zero]

theorem WeakMomentumOn.mono {smaller horizon : ℝ} {initialVelocity : Velocity}
    {velocity : ℝ → Velocity}
    (momentum : WeakMomentumOn horizon initialVelocity velocity)
    (ordered : smaller ≤ horizon) : WeakMomentumOn smaller initialVelocity velocity := by
  intro test admissible
  obtain ⟨integrable, initialIntegrable, identity⟩ := momentum test (admissible.mono ordered)
  refine ⟨integrable.mono_measure (spacetimeMeasure_mono ordered), initialIntegrable, ?_⟩
  rw [integral_spacetime_eq_of_vanishes_after ordered] at identity
  · exact identity
  · intro point after
    simp only [timeDerivative, spatialDerivative,
      fderiv_eq_zero_after_horizon admissible.2.2.1 after,
      ContinuousLinearMap.zero_apply, add_zero, inner_zero_right]

end EulerNonuniqueness
