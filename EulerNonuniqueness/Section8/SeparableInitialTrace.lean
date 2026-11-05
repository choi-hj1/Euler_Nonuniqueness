import EulerNonuniqueness.Section8.SeparableTransport

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.separableTest_initial_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity)
    {temporal : ℝ → ℝ} {spatial : Plane → ℝ}
    (temporalSmooth : ContDiff ℝ ∞ temporal) (temporalCompact : HasCompactSupport temporal)
    (temporalZero : ∀ time, horizon ≤ time → temporal time = 0)
    (spatialSmooth : ContDiff ℝ ∞ spatial) (spatialCompact : HasCompactSupport spatial)
    (momentIntegrable : ∀ time ∈ Icc 0 horizon, Integrable (fun position => omega time position * spatial position))
    (fluxIntegrable : ∀ time ∈ Icc 0 horizon, Integrable (fun position =>
      omega time position * fderiv ℝ spatial position (velocity time position))) :
    (∫ time in Ioo 0 horizon,
      (∫ position, omega time position * spatial position) * deriv temporal time +
      (∫ position, omega time position * fderiv ℝ spatial position (velocity time position)) * temporal time) +
      (∫ position, initial position * spatial position) * temporal 0 = 0 := by
  let test : ℝ × Plane → ℝ := fun point => temporal point.1 * spatial point.2
  have admissible : ScalarTestOn horizon test := by
    refine ⟨(temporalSmooth.comp contDiff_fst).mul (spatialSmooth.comp contDiff_snd), ?_, ?_⟩
    · exact (temporalCompact.isCompact.prod spatialCompact.isCompact).of_isClosed_subset
        (isClosed_tsupport _) tsupport_separableTest_subset
    · intro time position after
      simp only [test, temporalZero time after, zero_mul]
  let integrand : ℝ × Plane → ℝ := fun point => omega point.1 point.2 *
    (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))
  obtain ⟨integrable, initialIntegrable, equation⟩ := transport test admissible
  have innerEquality (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (∫ position, integrand (time, position)) =
        (∫ position, omega time position * spatial position) * deriv temporal time +
        (∫ position, omega time position * fderiv ℝ spatial position (velocity time position)) * temporal time := by
    have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    calc
      _ = ∫ position, (omega time position * spatial position) * deriv temporal time +
          (omega time position * fderiv ℝ spatial position (velocity time position)) * temporal time := by
        apply integral_congr_ae
        exact Eventually.of_forall fun position => by
          dsimp only [integrand, test]
          rw [timeDerivative_separable (temporalSmooth.differentiable (by simp)) (spatialSmooth.differentiable (by simp)),
            spatialDerivative_separable (temporalSmooth.differentiable (by simp)) (spatialSmooth.differentiable (by simp))]
          ring
      _ = _ := by
        rw [integral_add ((momentIntegrable time closedInside).mul_const _)
          ((fluxIntegrable time closedInside).mul_const _), integral_mul_const, integral_mul_const]
  have innerEqualityAE : (fun time => ∫ position, integrand (time, position)) =ᵐ[volume.restrict (Ioo 0 horizon)]
      fun time => (∫ position, omega time position * spatial position) * deriv temporal time +
        (∫ position, omega time position * fderiv ℝ spatial position (velocity time position)) * temporal time := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    exact innerEquality time inside
  have fubini := integral_prod integrand (show Integrable integrand
    ((volume.restrict (Ioo 0 horizon)).prod volume) from integrable)
  rw [integral_congr_ae innerEqualityAE] at fubini
  change (∫ point, integrand point ∂((volume.restrict (Ioo 0 horizon)).prod volume)) + _ = 0 at equation
  rw [fubini] at equation
  have initialEquality : (∫ position, initial position * test (0, position)) =
      (∫ position, initial position * spatial position) * temporal 0 := by
    calc
      _ = ∫ position, (initial position * spatial position) * temporal 0 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun position => by dsimp [test]; ring
      _ = _ := integral_mul_const _ _
  rwa [initialEquality] at equation

end EulerNonuniqueness
