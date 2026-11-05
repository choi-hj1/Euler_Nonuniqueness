import EulerNonuniqueness.General.LocalSecondRegularity
import EulerNonuniqueness.General.RelativeCubicTaylor

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] relativeCubicBilinearGroup relativeCubicBilinearSpace
  relativeCubicThirdGroup relativeCubicThirdSpace

theorem exists_third_lipschitz_closedBall
    (function : Space → Space) (base : Space)
    (first : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ function point)
    (regular : HasLipschitzSecondDerivativeNear (fderiv ℝ function) base) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ constant : NNReal,
      (∀ point ∈ closedBall base radius,
        DifferentiableAt ℝ function point ∧ DifferentiableAt ℝ (fderiv ℝ function) point ∧
        DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ function)) point) ∧
      LipschitzOnWith constant (fderiv ℝ (fderiv ℝ (fderiv ℝ function))) (closedBall base radius) := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular.2.2
  have combined : neighborhood ∩ {point | DifferentiableAt ℝ function point ∧
      DifferentiableAt ℝ (fderiv ℝ function) point ∧
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ function)) point} ∈ 𝓝 base := by
    apply inter_mem nearby
    filter_upwards [first, regular.1.1, regular.2.1] with point firstActual secondActual thirdActual
    exact ⟨firstActual, secondActual, thirdActual⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  have smaller : closedBall base (radius / 2) ⊆
      neighborhood ∩ {point | DifferentiableAt ℝ function point ∧
        DifferentiableAt ℝ (fderiv ℝ function) point ∧
        DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ function)) point} := by
    intro point member
    apply contained
    have bound := mem_closedBall.mp member
    apply mem_ball.mpr
    linarith
  exact ⟨radius / 2, by positivity, constant,
    fun point member => (smaller member).2, lipschitz.mono fun point member => (smaller member).1⟩

end

end EulerNonuniqueness.General
