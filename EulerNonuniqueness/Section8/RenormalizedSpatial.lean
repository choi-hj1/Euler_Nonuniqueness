import EulerNonuniqueness.Section8.MollifiedTransport

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem integral_renormalized_spatial_transport
    {vorticity : Vorticity} {radius : ℝ} (integrable : Integrable vorticity)
    (member : MemLp vorticity (ENNReal.ofReal 4) volume) (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {regularized test : Plane → ℝ} {renormalization : ℝ → ℝ}
    (regularizedSmooth : ContDiff ℝ 1 regularized)
    (renormalizationSmooth : ContDiff ℝ 1 renormalization)
    (testSmooth : ContDiff ℝ 1 test) (testCompact : HasCompactSupport test) :
    Integrable (fun position => renormalization (regularized position) *
      fderiv ℝ test position (biotSavart vorticity position)) ∧
    Integrable (fun position => deriv renormalization (regularized position) *
      fderiv ℝ regularized position (biotSavart vorticity position) * test position) ∧
    (∫ position, renormalization (regularized position) *
      fderiv ℝ test position (biotSavart vorticity position)) +
      (∫ position, deriv renormalization (regularized position) *
        fderiv ℝ regularized position (biotSavart vorticity position) * test position) = 0 := by
  have velocityContinuous := continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    member (by norm_num) radiusNonnegative supportBound
  have firstContinuous : Continuous (fun position => renormalization (regularized position) *
      fderiv ℝ test position (biotSavart vorticity position)) :=
    (renormalizationSmooth.continuous.comp regularizedSmooth.continuous).mul
      ((testSmooth.continuous_fderiv (by simp)).clm_apply velocityContinuous)
  have firstCompact : HasCompactSupport (fun position => renormalization (regularized position) *
      fderiv ℝ test position (biotSavart vorticity position)) := by
    apply (testCompact.fderiv (𝕜 := ℝ)).mono
    intro position nonzero
    apply Function.mem_support.mpr
    intro zero
    exact nonzero (by simp [zero])
  have secondContinuous : Continuous (fun position => deriv renormalization (regularized position) *
      fderiv ℝ regularized position (biotSavart vorticity position) * test position) :=
    (((renormalizationSmooth.continuous_deriv (by simp)).comp regularizedSmooth.continuous).mul
      ((regularizedSmooth.continuous_fderiv (by simp)).clm_apply velocityContinuous)).mul testSmooth.continuous
  have firstIntegrable := firstContinuous.integrable_of_hasCompactSupport firstCompact (μ := volume)
  have secondIntegrable := secondContinuous.integrable_of_hasCompactSupport testCompact.mul_left (μ := volume)
  refine ⟨firstIntegrable, secondIntegrable, ?_⟩
  have divergence := (divergenceFree_biotSavart_of_integrable_support integrable supportBound
    ((renormalizationSmooth.comp regularizedSmooth).mul testSmooth) testCompact.mul_left).2
  have derivative (position : Plane) :
      fderiv ℝ (fun point => renormalization (regularized point) * test point) position
        (biotSavart vorticity position) =
      renormalization (regularized position) * fderiv ℝ test position (biotSavart vorticity position) +
        deriv renormalization (regularized position) *
          fderiv ℝ regularized position (biotSavart vorticity position) * test position := by
    have regularizedDifferentiable := regularizedSmooth.differentiable (by simp)
    have renormalizationDifferentiable := renormalizationSmooth.differentiable (by simp)
    change (fderiv ℝ (fun point => (renormalization ∘ regularized) point * test point) position)
      (biotSavart vorticity position) = _
    rw [fderiv_mul ((renormalizationDifferentiable (regularized position)).comp position
      (regularizedDifferentiable position)) (testSmooth.differentiable (by simp) position)]
    rw [fderiv_comp position (renormalizationDifferentiable (regularized position))
      (regularizedDifferentiable position)]
    simp [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul, mul_comm, mul_left_comm, mul_assoc]
  change (∫ position, fderiv ℝ (fun point => renormalization (regularized point) * test point) position
    (biotSavart vorticity position)) = 0 at divergence
  simp_rw [derivative] at divergence
  rwa [integral_add firstIntegrable secondIntegrable] at divergence

end EulerNonuniqueness
