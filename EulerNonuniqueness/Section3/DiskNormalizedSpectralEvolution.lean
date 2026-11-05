import EulerNonuniqueness.Section3.ContourNormalizedEvolution
import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseBounds

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

local instance normalizedSpectralEvolutionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd

def diskNormalizedSpectralCoordinate (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization data)

def diskNormalizedSpectralError (data error : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization data)
    (fderiv ℝ contourAreaCentroidNormalization data error)

theorem diskNormalizedSpectralCoordinate_exists_uniform_evolution :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ} {error : PeriodicC1HolderHalf},
      ‖curve time - standardCircleBanach‖ ≤ radius →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time →
      diskSpectralTubularArea (diskNormalizedSpectralCoordinate (curve time)) = Real.pi ∧
      HasDerivAt (fun current => diskNormalizedSpectralCoordinate (curve current))
        (frequency • diskSpectralTubularEulerField (diskNormalizedSpectralCoordinate (curve time)) +
          diskNormalizedSpectralError (curve time) error) time ∧
      ‖diskNormalizedSpectralError (curve time) error‖ ≤ constant * ‖error‖ := by
  obtain ⟨normalRadius, normalPositive, normalConstant, normalOne, normalEvolution⟩ :=
    contourAreaCentroidNormalization_exists_uniform_evolution
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBounds, _, _⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds
  have normalContinuous : ContinuousAt contourAreaCentroidNormalization standardCircleBanach :=
    (contourAreaCentroidNormalization_differentiableAt standardCircleBanach (by simp)).continuousAt
  have normalLimit : Tendsto contourAreaCentroidNormalization (𝓝 standardCircleBanach) (𝓝 standardCircleBanach) := by
    simpa only [contourAreaCentroidNormalization_circle] using normalContinuous.tendsto
  have normalizedValid : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖contourAreaCentroidNormalization data - standardCircleBanach‖ < inverseRadius ∧
      diskSpectralTubularArea (diskNormalizedSpectralCoordinate data) = contourAreaFunctional (contourAreaCentroidNormalization data) ∧
      diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization data)
        (diskEulerRotatingField (contourAreaCentroidNormalization data)) =
        diskSpectralTubularEulerField (diskNormalizedSpectralCoordinate data) := by
    filter_upwards [normalLimit.eventually (Metric.ball_mem_nhds _ inversePositive),
      normalLimit.eventually diskPhysicalSpectralCoordinate_eventually_area,
      normalLimit.eventually diskPhysicalSpectralCoordinate_eventually_inverse_derivative]
      with data nearby area actual
    exact ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using nearby, area, actual.2.2⟩
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp normalizedValid
  let radius := min normalRadius (outerRadius / 2)
  let constant := inverseConstant * normalConstant
  have constantOne : 1 ≤ constant := by dsimp [constant]; nlinarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro curve time frequency error small derivative
  obtain ⟨area, _, normalDerivative, errorBound⟩ :=
    normalEvolution (small.trans (min_le_left _ _)) derivative
  obtain ⟨normalNear, spectralArea, selfIdentity⟩ := contained
    (show dist (curve time) standardCircleBanach < outerRadius by
      rw [dist_eq_norm]
      exact (small.trans (min_le_right _ _)).trans_lt (by linarith))
  obtain ⟨inverseDerivative, inverseBound⟩ := inverseBounds _ normalNear.le
  have actual := hasDerivAt_diskPhysicalSpectralCoordinate_of_equation normalDerivative inverseDerivative selfIdentity
  refine ⟨spectralArea.trans area, actual, ?_⟩
  unfold diskNormalizedSpectralError
  exact ((diskPhysicalSpectralInverseDerivative (contourAreaCentroidNormalization (curve time))).le_opNorm _).trans
    ((mul_le_mul inverseBound errorBound (norm_nonneg _) (by linarith)).trans_eq (by dsimp only [constant]; ring))

end EulerNonuniqueness.Paper
