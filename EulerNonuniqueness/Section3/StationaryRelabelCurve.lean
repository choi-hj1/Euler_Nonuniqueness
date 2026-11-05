import EulerNonuniqueness.General.LinearExponentialCurve
import EulerNonuniqueness.Section3.C1HolderContinuousOperations
import EulerNonuniqueness.Section3.ComplexHolderInstances
import EulerNonuniqueness.Section3.ContourLocalEvolution
import EulerNonuniqueness.Section3.ParameterizedDiskEquilibria

namespace EulerNonuniqueness.Paper

open Filter
open scoped Topology

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabelHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance relabelC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance relabelC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance relabelC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance relabelC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance relabelOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance relabelOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance relabelOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskRelabelGenerator (angular : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  c1ProductCLM (Complex.I • angular)

def diskRelabelCurve (angular : PeriodicC1HolderHalf) (parameter : ℝ) : PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.linearExponentialCurve (diskRelabelGenerator angular) standardCircleBanach parameter

theorem diskRelabelCurve_zero (angular : PeriodicC1HolderHalf) :
    diskRelabelCurve angular 0 = standardCircleBanach := by
  unfold diskRelabelCurve
  with_reducible
    exact EulerNonuniqueness.General.linearExponentialCurve_zero (Space := PeriodicC1HolderHalf) _ _

theorem diskRelabelCurve_hasDerivAt (angular : PeriodicC1HolderHalf) (parameter : ℝ) :
    HasDerivAt (diskRelabelCurve angular)
      (diskRelabelGenerator angular (diskRelabelCurve angular parameter)) parameter := by
  unfold diskRelabelCurve
  with_reducible
    exact EulerNonuniqueness.General.linearExponentialCurve_hasDerivAt (Space := PeriodicC1HolderHalf) _ _ _

theorem diskRelabelCurve_analyticAt (angular : PeriodicC1HolderHalf) (parameter : ℝ) :
    AnalyticAt ℝ (diskRelabelCurve angular) parameter := by
  unfold diskRelabelCurve
  with_reducible
    exact EulerNonuniqueness.General.linearExponentialCurve_analyticAt (Space := PeriodicC1HolderHalf) _ _ _

theorem diskRelabelCurve_value (angular : PeriodicC1HolderHalf) (parameter label : ℝ) :
    (diskRelabelCurve angular parameter).val.1 label =
      Complex.exp ((parameter : ℂ) * (Complex.I * angular.val.1 label)) * standardCircle label := by
  unfold diskRelabelCurve
  have generic := EulerNonuniqueness.General.linearExponentialCurve_evaluation (Space := PeriodicC1HolderHalf)
      (diskRelabelGenerator angular) standardCircleBanach (contourLabelEvaluation label)
      (Complex.I * angular.val.1 label) (fun _ => rfl) parameter
  unfold contourLabelEvaluation at generic
  exact generic

theorem diskRelabelCurve_unit_norm (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) (parameter label : ℝ) :
    ‖(diskRelabelCurve angular parameter).val.1 label‖ = 1 := by
  have imaginaryZero : (angular.val.1 label).im = 0 := by
    have imaginary := congrArg Complex.im (realValues label)
    simp only [Complex.star_def, Complex.conj_im] at imaginary
    linarith
  rw [diskRelabelCurve_value, norm_mul, standardCircle_norm, mul_one, Complex.norm_exp]
  simp [Complex.mul_re, imaginaryZero]

theorem diskRelabelCurve_first_jet (angular : PeriodicC1HolderHalf) :
    HasDerivAt (diskRelabelCurve angular) (c1Product (Complex.I • angular) standardCircleBanach) 0 := by
  have actual := diskRelabelCurve_hasDerivAt angular 0
  rw [diskRelabelCurve_zero] at actual
  exact actual

theorem diskRelabelCurve_second_jet (angular : PeriodicC1HolderHalf) :
    HasDerivAt (fun parameter => diskRelabelGenerator angular (diskRelabelCurve angular parameter))
      (-c1Product standardCircleBanach (c1Product angular angular)) 0 := by
  have actual : HasDerivAt (fun parameter => diskRelabelGenerator angular (diskRelabelCurve angular parameter))
      (diskRelabelGenerator angular (diskRelabelGenerator angular (diskRelabelCurve angular 0))) (0 : ℝ) := by
    unfold diskRelabelCurve
    with_reducible
      exact EulerNonuniqueness.General.linearExponentialCurve_second_hasDerivAt (Space := PeriodicC1HolderHalf)
        (diskRelabelGenerator angular) standardCircleBanach (0 : ℝ)
  rw [diskRelabelCurve_zero] at actual
  have derivativeEquality : diskRelabelGenerator angular (diskRelabelGenerator angular standardCircleBanach) =
      -c1Product standardCircleBanach (c1Product angular angular) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (Complex.I * angular.val.1 label) * ((Complex.I * angular.val.1 label) * standardCircle label) =
      -(standardCircle label * (angular.val.1 label * angular.val.1 label))
    linear_combination (standardCircle label * angular.val.1 label ^ 2) * Complex.I_sq
  rw [derivativeEquality] at actual
  exact actual

theorem diskRelabelCurve_eventually_stationary (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    ∀ᶠ parameter in 𝓝 (0 : ℝ), extendedContourVelocity (diskRelabelCurve angular parameter) -
      (Complex.I / 2) • diskRelabelCurve angular parameter = 0 := by
  have convergence : Tendsto (fun parameter => ‖diskRelabelCurve angular parameter - standardCircleBanach‖)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have actual := (diskRelabelCurve_analyticAt angular 0).continuousAt.tendsto.dist
      (tendsto_const_nhds (x := standardCircleBanach))
    have distance (value : PeriodicC1HolderHalf) : dist value standardCircleBanach = ‖value - standardCircleBanach‖ :=
      dist_eq_norm value standardCircleBanach
    simpa only [diskRelabelCurve_zero, dist_self, distance] using actual
  have small := convergence.eventually (eventually_lt_nhds
    (lt_min (by norm_num : (0 : ℝ) < 1 / 3) (by positivity : 0 < 2 / (3 * Real.pi))))
  filter_upwards [small] with parameter close
  have radiusSmall := lt_of_lt_of_le close (min_le_left _ _)
  have chordSmall := lt_of_lt_of_le close (min_le_right _ _)
  have chartSmall : ‖diskRelabelCurve angular parameter - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) :=
    lt_min (radiusSmall.trans (by norm_num)) chordSmall
  rw [extendedContourVelocity_eq _ chartSmall]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change contourVelocity (diskRelabelCurve angular parameter).val.1
      (diskRelabelCurve angular parameter).val.2.val.1 label (-Real.pi) Real.pi -
    (Complex.I / 2) * (diskRelabelCurve angular parameter).val.1 label = 0
  exact parameterizedDisk_rotatingFrame_stationary _ radiusSmall chordSmall
    (diskRelabelCurve_unit_norm angular realValues parameter) label

end

end EulerNonuniqueness.Paper
