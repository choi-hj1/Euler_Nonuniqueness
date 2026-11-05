import EulerNonuniqueness.Section3.DiskSpectralUniformSlope
import EulerNonuniqueness.Section3.DiskNormalizedSpectralEvolution
import EulerNonuniqueness.Section3.DiskNormalizedQuadraticObservable

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance normalizedUniformSlopeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskNormalizedQuadraticObservable_eq_coordinate (data : PeriodicC1HolderHalf) :
    diskNormalizedQuadraticObservable data =
      EulerNonuniqueness.General.quadraticCoordinate
        (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (diskNormalizedSpectralCoordinate data))) 1
        (diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate data)) := rfl

theorem diskNormalizedQuadraticObservable_exists_uniform_norm_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ} {error : PeriodicC1HolderHalf},
      ‖curve time - standardCircleBanach‖ ≤ radius →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time →
      ∀ threshold : ℝ,
      constant * (|frequency| * ‖diskPhysicalTransverseProjection
        (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 + ‖error‖) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖diskPhysicalScaledGroup frequency (-current)
          (diskNormalizedQuadraticObservable (curve current))‖) time later < threshold := by
  obtain ⟨evolutionRadius, evolutionPositive, evolutionConstant, evolutionOne, evolution⟩ :=
    diskNormalizedSpectralCoordinate_exists_uniform_evolution
  obtain ⟨slopeRadius, slopePositive, slopeConstant, slopeOne, slopes⟩ :=
    diskSpectralScaledCoordinate_exists_uniform_norm_slope
  have normalizationContinuous : ContinuousAt contourAreaCentroidNormalization standardCircleBanach :=
    (contourAreaCentroidNormalization_differentiableAt standardCircleBanach (by simp)).continuousAt
  have normalizationLimit : Tendsto contourAreaCentroidNormalization (𝓝 standardCircleBanach) (𝓝 standardCircleBanach) := by
    simpa only [contourAreaCentroidNormalization_circle] using normalizationContinuous.tendsto
  have coordinateLimit : Tendsto diskNormalizedSpectralCoordinate (𝓝 standardCircleBanach) (𝓝 (0 : PeriodicC1HolderHalf)) := by
    have outer : Tendsto diskPhysicalSpectralCoordinate (𝓝 standardCircleBanach) (𝓝 (0 : PeriodicC1HolderHalf)) := by
      simpa only [diskPhysicalSpectralCoordinate_circle] using diskPhysicalSpectralCoordinate_continuousAt_circle.tendsto
    exact outer.comp normalizationLimit
  have neutralLimit := diskRelabelNeutralCLM.continuous.tendsto 0 |>.comp coordinateLimit
  have relativeLimit := coordinateLimit.sub neutralLimit
  have transverseLimit := diskPhysicalTransverseProjection.continuous.tendsto 0 |>.comp coordinateLimit
  have sizeLimit : Tendsto
      (fun data => ‖diskRelabelNeutralCLM (diskNormalizedSpectralCoordinate data)‖ +
        ‖diskNormalizedSpectralCoordinate data - diskRelabelNeutralCLM (diskNormalizedSpectralCoordinate data)‖)
      (𝓝 standardCircleBanach) (𝓝 (0 : ℝ)) := by
    simpa only [map_zero, sub_zero, norm_zero, zero_add] using neutralLimit.norm.add relativeLimit.norm
  have transverseNormLimit : Tendsto
      (fun data => ‖diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate data)‖)
      (𝓝 standardCircleBanach) (𝓝 (0 : ℝ)) := by
    simpa only [map_zero, norm_zero] using transverseLimit.norm
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    ((sizeLimit.eventually (eventually_lt_nhds slopePositive)).and
      (transverseNormLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))))
  let radius := min evolutionRadius (outerRadius / 2)
  let constant := slopeConstant * evolutionConstant
  have constantOne : 1 ≤ constant := by dsimp [constant]; nlinarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro curve time frequency error small derivative threshold strict
  obtain ⟨area, equation, errorBound⟩ := evolution (small.trans (min_le_left _ _)) derivative
  obtain ⟨tubeSmall, transverseSmall⟩ := contained
    (show dist (curve time) standardCircleBanach < outerRadius by
      rw [dist_eq_norm]
      exact (small.trans (min_le_right _ _)).trans_lt (by linarith))
  have scalarBound : slopeConstant * (|frequency| * ‖diskPhysicalTransverseProjection
      (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 +
        ‖diskNormalizedSpectralError (curve time) error‖) < threshold := by
    have selfNonnegative : 0 ≤ |frequency| * ‖diskPhysicalTransverseProjection
        (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 := by positivity
    have first := add_le_add_left errorBound (|frequency| * ‖diskPhysicalTransverseProjection
      (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3)
    have enlarged := mul_le_mul_of_nonneg_right evolutionOne selfNonnegative
    have bound : |frequency| * ‖diskPhysicalTransverseProjection (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 +
        ‖diskNormalizedSpectralError (curve time) error‖ ≤
        evolutionConstant * (|frequency| * ‖diskPhysicalTransverseProjection
          (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 + ‖error‖) := by
      apply first.trans
      rw [mul_add]
      exact add_le_add_right (by simpa only [one_mul] using enlarged) _
    exact ((mul_le_mul_of_nonneg_left bound (by linarith)).trans_eq (by dsimp only [constant]; ring)).trans_lt strict
  have actual := slopes equation tubeSmall.le area transverseSmall.le threshold scalarBound
  simp only [diskNormalizedQuadraticObservable_eq_coordinate]
  exact actual

end EulerNonuniqueness.Paper
