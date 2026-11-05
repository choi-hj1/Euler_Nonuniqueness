import EulerNonuniqueness.Section8.SeparableTests

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.separableTest_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity)
    {temporal : ℝ → ℝ} {spatial : Plane → ℝ}
    (temporalSmooth : ContDiff ℝ ∞ temporal)
    (temporalCompact : HasCompactSupport temporal)
    (temporalSupport : tsupport temporal ⊆ Ioo 0 horizon)
    (spatialSmooth : ContDiff ℝ ∞ spatial) (spatialCompact : HasCompactSupport spatial)
    (momentIntegrable : ∀ time ∈ Icc 0 horizon,
      Integrable (fun position => omega time position * spatial position))
    (fluxIntegrable : ∀ time ∈ Icc 0 horizon, Integrable (fun position =>
      omega time position * fderiv ℝ spatial position (velocity time position))) :
    IntegrableOn (fun time =>
      (∫ position, omega time position * spatial position) * deriv temporal time +
      (∫ position, omega time position *
        fderiv ℝ spatial position (velocity time position)) * temporal time) (Ioo 0 horizon) ∧
    (∫ time in Ioo 0 horizon,
      (∫ position, omega time position * spatial position) * deriv temporal time +
      (∫ position, omega time position *
        fderiv ℝ spatial position (velocity time position)) * temporal time) = 0 := by
  let test : ℝ × Plane → ℝ := fun point => temporal point.1 * spatial point.2
  let integrand : ℝ × Plane → ℝ := fun point => omega point.1 point.2 *
    (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))
  obtain ⟨integrable, initialIntegrable, equation⟩ := transport test
    (scalarTestOn_separable temporalSmooth temporalCompact temporalSupport spatialSmooth spatialCompact)
  have temporalDifferentiable := temporalSmooth.differentiable (by simp)
  have spatialDifferentiable := spatialSmooth.differentiable (by simp)
  have innerEquality (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (∫ position, integrand (time, position)) =
        (∫ position, omega time position * spatial position) * deriv temporal time +
        (∫ position, omega time position *
          fderiv ℝ spatial position (velocity time position)) * temporal time := by
    have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    calc
      _ = ∫ position, (omega time position * spatial position) * deriv temporal time +
          (omega time position * fderiv ℝ spatial position (velocity time position)) *
            temporal time := by
        apply integral_congr_ae
        exact Eventually.of_forall fun position => by
          dsimp only [integrand, test]
          rw [timeDerivative_separable temporalDifferentiable spatialDifferentiable,
            spatialDerivative_separable temporalDifferentiable spatialDifferentiable]
          ring
      _ = _ := by
        rw [integral_add ((momentIntegrable time closedInside).mul_const _)
          ((fluxIntegrable time closedInside).mul_const _), integral_mul_const, integral_mul_const]
  have innerEqualityAE :
      (fun time => ∫ position, integrand (time, position)) =ᵐ[volume.restrict (Ioo 0 horizon)]
        fun time => (∫ position, omega time position * spatial position) * deriv temporal time +
          (∫ position, omega time position *
            fderiv ℝ spatial position (velocity time position)) * temporal time := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    exact innerEquality time inside
  have productIntegrable : Integrable integrand
      ((volume.restrict (Ioo 0 horizon)).prod volume) := integrable
  refine ⟨productIntegrable.integral_prod_left.congr innerEqualityAE, ?_⟩
  have temporalAtZero : temporal 0 = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    exact fun inside => lt_irrefl 0 (temporalSupport inside).1
  have initialZero : (∫ position, initial position * test (0, position)) = 0 := by
    simp [test, temporalAtZero]
  have fubini := integral_prod integrand productIntegrable
  rw [integral_congr_ae innerEqualityAE] at fubini
  change (∫ point, integrand point ∂spacetimeMeasure horizon) + _ = 0 at equation
  rw [initialZero, add_zero] at equation
  exact fubini.symm.trans equation

end EulerNonuniqueness
