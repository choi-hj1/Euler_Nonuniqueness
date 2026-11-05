import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeError

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance normalizedTrueAngularErrorRelativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskNormalizedTrueAngularError (data error : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskNeutralCLM (diskNormalizedSpectralError data error)

theorem diskNormalizedTrueAngularError_exists_uniform_pair_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ first final firstError finalError : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
      ‖diskNormalizedTrueAngularError first firstError - diskNormalizedTrueAngularError final finalError‖ ≤
        constant * (‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖) := by
  obtain ⟨radius, positive, normalConstant, normalOne, normals⟩ := diskNormalizedSpectralError_exists_relative_ball
  let constant := ‖diskNeutralCLM‖ * normalConstant + 1
  have normalNonnegative : 0 ≤ normalConstant := by linarith
  have productNonnegative : 0 ≤ ‖diskNeutralCLM‖ * normalConstant := by positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨radius, positive, constant, constantOne, ?_⟩
  intro first final firstError finalError firstInside finalInside
  have actual := (diskNeutralCLM.le_opNorm
    (diskNormalizedSpectralError first firstError - diskNormalizedSpectralError final finalError)).trans
      (mul_le_mul_of_nonneg_left (normals first final firstError finalError firstInside finalInside) (norm_nonneg diskNeutralCLM))
  rw [map_sub] at actual
  have coefficientLe : ‖diskNeutralCLM‖ * normalConstant ≤ constant := by dsimp only [constant]; linarith
  have scalar := mul_le_mul_of_nonneg_right coefficientLe
    (by positivity : 0 ≤ ‖firstError - finalError‖ + ‖first - final‖ * ‖finalError‖)
  exact (actual.trans_eq (by ring)).trans scalar

end EulerNonuniqueness.Paper
