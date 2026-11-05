import EulerNonuniqueness.Section3.ContourMomentRealScaling
import EulerNonuniqueness.Section3.MovingCentroidGaugeConservation
import EulerNonuniqueness.Section3.DiskAreaDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance areaCentroidNormalizationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance areaCentroidNormalizationC1Semi : SeminormedAddCommGroup PeriodicC1HolderHalf :=
  areaCentroidNormalizationC1Group.toSeminormedAddCommGroup

local instance areaCentroidNormalizationC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def contourCentroidRecenter (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  data - c1ConstantCLM (contourCentroidFunctional data)

def contourAreaCentroidNormalization (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  Real.sqrt (Real.pi / contourAreaFunctional data) • contourCentroidRecenter data

theorem contourAreaFunctional_recenter (data : PeriodicC1HolderHalf) :
    contourAreaFunctional (contourCentroidRecenter data) = contourAreaFunctional data := by
  have actual := contourAreaFunctional_translate data (-contourCentroidFunctional data)
  change contourAreaFunctional (data + c1ConstantCLM (-contourCentroidFunctional data)) = _ at actual
  simpa only [contourCentroidRecenter, map_neg, sub_eq_add_neg] using actual

theorem contourCentroidFunctional_recenter (data : PeriodicC1HolderHalf)
    (area : contourAreaFunctional data ≠ 0) :
    contourCentroidFunctional (contourCentroidRecenter data) = 0 := by
  have actual := contourCentroidFunctional_translate data (-contourCentroidFunctional data) area
  change contourCentroidFunctional (data + c1ConstantCLM (-contourCentroidFunctional data)) = _ at actual
  simpa only [contourCentroidRecenter, map_neg, sub_eq_add_neg, add_neg_cancel] using actual

theorem contourAreaCentroidNormalization_area (data : PeriodicC1HolderHalf)
    (positive : 0 < contourAreaFunctional data) :
    contourAreaFunctional (contourAreaCentroidNormalization data) = Real.pi := by
  rw [contourAreaCentroidNormalization, contourAreaFunctional_real_smul, contourAreaFunctional_recenter,
    Real.sq_sqrt (div_nonneg Real.pi_pos.le positive.le)]
  exact div_mul_cancel₀ Real.pi positive.ne'

theorem contourAreaCentroidNormalization_centroid (data : PeriodicC1HolderHalf)
    (positive : 0 < contourAreaFunctional data) :
    contourCentroidFunctional (contourAreaCentroidNormalization data) = 0 := by
  have scalePositive : 0 < Real.sqrt (Real.pi / contourAreaFunctional data) :=
    Real.sqrt_pos.2 (div_pos Real.pi_pos positive)
  rw [contourAreaCentroidNormalization, contourCentroidFunctional_real_smul _ _ scalePositive.ne',
    contourCentroidFunctional_recenter data positive.ne', smul_zero]

theorem contourCentroidRecenter_differentiableAt (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : DifferentiableAt ℝ contourCentroidRecenter data := by
  have identity : DifferentiableAt ℝ (fun current : PeriodicC1HolderHalf => current) data := differentiableAt_id
  have centroid := (analyticAt_contourCentroidFunctional data small).differentiableAt
  have constant : DifferentiableAt ℝ (fun current => c1ConstantCLM (contourCentroidFunctional current)) data :=
    DifferentiableAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℂ) (G := PeriodicC1HolderHalf)
      data c1ConstantCLM.differentiableAt centroid
  exact identity.sub constant

theorem contourAreaCentroidNormalization_differentiableAt (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    DifferentiableAt ℝ contourAreaCentroidNormalization data := by
  have positive := contourAreaFunctional_pos data small
  have areaDerivative := (analyticAt_contourAreaFunctional data).differentiableAt
  have numerator : DifferentiableAt ℝ (fun _ : PeriodicC1HolderHalf => Real.pi) data := differentiableAt_const Real.pi
  have ratioDerivative : DifferentiableAt ℝ (fun current => Real.pi / contourAreaFunctional current) data := by
    simpa only [div_eq_mul_inv] using numerator.mul (areaDerivative.inv positive.ne')
  have scaleDerivative := ratioDerivative.sqrt (ne_of_gt (div_pos Real.pi_pos positive))
  exact scaleDerivative.smul (contourCentroidRecenter_differentiableAt data small)

theorem contourCentroidRecenter_circle : contourCentroidRecenter standardCircleBanach = standardCircleBanach := by
  simp only [contourCentroidRecenter, contourCentroidFunctional_standardCircle_zero, map_zero, sub_zero]

theorem contourAreaCentroidNormalization_circle :
    contourAreaCentroidNormalization standardCircleBanach = standardCircleBanach := by
  rw [contourAreaCentroidNormalization, contourAreaFunctional_standardCircle, div_self Real.pi_ne_zero,
    Real.sqrt_one, one_smul, contourCentroidRecenter_circle]

theorem contourAreaCentroidNormalization_eventually_admissible :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)) ∧
      0 < contourAreaFunctional data ∧
      ‖contourCentroidRecenter data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) ∧
      ‖contourAreaCentroidNormalization data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
  have circleSmall : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by simp
  have thresholdPositive : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have recenterLimit : Tendsto contourCentroidRecenter (𝓝 standardCircleBanach) (𝓝 standardCircleBanach) := by
    simpa only [contourCentroidRecenter_circle] using
      (contourCentroidRecenter_differentiableAt standardCircleBanach circleSmall).continuousAt.tendsto
  have normalizationLimit : Tendsto contourAreaCentroidNormalization (𝓝 standardCircleBanach) (𝓝 standardCircleBanach) := by
    simpa only [contourAreaCentroidNormalization_circle] using
      (contourAreaCentroidNormalization_differentiableAt standardCircleBanach circleSmall).continuousAt.tendsto
  have nearby : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)) := by
    simpa only [Metric.ball, dist_eq_norm] using
      Metric.ball_mem_nhds standardCircleBanach (show (0 : ℝ) < min (1 / 3) (2 / (3 * Real.pi)) by positivity)
  have recentered := recenterLimit.eventually (Metric.ball_mem_nhds standardCircleBanach thresholdPositive)
  have normalized := normalizationLimit.eventually (Metric.ball_mem_nhds standardCircleBanach thresholdPositive)
  filter_upwards [nearby, recentered, normalized] with data small recenterSmall normalizedSmall
  refine ⟨small, contourAreaFunctional_pos data (small.trans_le (min_le_left _ _)), ?_, ?_⟩
  · simpa only [dist_eq_norm] using recenterSmall
  · simpa only [dist_eq_norm] using normalizedSmall

end EulerNonuniqueness.Paper
