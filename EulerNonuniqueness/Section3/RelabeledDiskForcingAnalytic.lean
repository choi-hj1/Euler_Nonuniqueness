import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive
import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.General.AnalyticExponentialEvaluation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabeledAnalyticC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

def diskRelabelGeneratorCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  c1ProductCLM.comp (c1ProductCLM (c1Constant Complex.I))

theorem diskRelabelGeneratorCLM_apply (angular : PeriodicC1HolderHalf) :
    diskRelabelGeneratorCLM angular = diskRelabelGenerator angular := by
  change c1ProductCLM (c1Product (c1Constant Complex.I) angular) = c1ProductCLM (Complex.I • angular)
  congr 1
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem diskRelabelMap_analyticAt (angular : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (fun current => diskRelabelCurve current 1) angular := by
  have evaluation : AnalyticAt ℝ
      (fun current => NormedSpace.exp ℝ (diskRelabelGeneratorCLM current) standardCircleBanach) angular := by
    with_reducible
      exact EulerNonuniqueness.General.analyticAt_exponential_generator_evaluation
        (Space := PeriodicC1HolderHalf) diskRelabelGeneratorCLM standardCircleBanach angular
  apply evaluation.congr
  filter_upwards [] with current
  simp only [ContinuousLinearMap.apply_apply, diskRelabelCurve,
    EulerNonuniqueness.General.linearExponentialCurve, one_smul, diskRelabelGeneratorCLM_apply]

theorem c1NaturalPower_analyticAt (degree : ℕ) (data : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (fun current => c1NaturalPower current degree) data := by
  induction degree with
  | zero => exact analyticAt_const
  | succ degree induction =>
    exact (ContinuousLinearMap.analyticAt_bilinear (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf) c1ProductCLM
      (data, c1NaturalPower data degree)).comp₂
      (f := fun current : PeriodicC1HolderHalf => current) (g := fun current => c1NaturalPower current degree)
      ((ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).analyticAt data) induction

theorem relabeledDiskForcingMode_analyticAt (degree : ℕ) (angular : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (fun current => relabeledDiskForcingMode current degree) angular := by
  have powers := (c1NaturalPower_analyticAt (degree + 1) (diskRelabelCurve angular 1)).comp
    (f := fun current : PeriodicC1HolderHalf => diskRelabelCurve current 1)
    (diskRelabelMap_analyticAt angular)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    c1ConjugateCLM (c1NaturalPower (diskRelabelCurve angular 1) (degree + 1))).comp
    (f := fun current : PeriodicC1HolderHalf => c1NaturalPower (diskRelabelCurve current 1) (degree + 1)) powers

theorem relabeledDiskForcingPrimitive_analyticAt (degree : ℕ) (frequency : ℝ)
    (amplitude : ℝ → ℂ) (time : ℝ) (angular : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (fun current => relabeledDiskForcingPrimitive current degree frequency amplitude time) angular := by
  let scalar := diskForcingPrimitiveFactor degree frequency * amplitude time * diskForcingPhase degree frequency time
  have multiplier : AnalyticAt ℝ (c1ProductCLM (c1Constant scalar)) (relabeledDiskForcingMode angular degree) :=
    ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (c1ProductCLM (c1Constant scalar)) (relabeledDiskForcingMode angular degree)
  have composed := multiplier.comp (f := fun current : PeriodicC1HolderHalf => relabeledDiskForcingMode current degree)
    (relabeledDiskForcingMode_analyticAt degree angular)
  apply composed.congr
  filter_upwards [] with current
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

end

end EulerNonuniqueness.Paper
