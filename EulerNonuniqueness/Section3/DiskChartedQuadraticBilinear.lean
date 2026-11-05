import EulerNonuniqueness.Section3.DiskChartedSecondDifferentiable
import EulerNonuniqueness.General.BilinearOperatorCalculus
import EulerNonuniqueness.General.LocalIntervalContinuity

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance chartedBilinearC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance chartedBilinearC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance chartedBilinearOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedBilinearOperatorModule : Module ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance chartedBilinearOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedBilinearOperatorUniformAdd : IsUniformAddGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
local instance chartedBilinearOperatorContinuousAdd : ContinuousAdd (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  (inferInstance : IsTopologicalAddGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)).toContinuousAdd
local instance chartedBilinearGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedBilinearModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)

def diskChartedQuadraticBilinear : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  @SMul.smul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (inferInstance : SMul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf))
    (1 / 2) (fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf))

theorem diskChartedQuadraticBilinear_apply (first second : PeriodicC1HolderHalf) :
    diskChartedQuadraticBilinear first second =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) first second := rfl

theorem diskChartedQuadraticBilinear_symmetric (first second : PeriodicC1HolderHalf) :
    diskChartedQuadraticBilinear first second = diskChartedQuadraticBilinear second first := by
  rw [diskChartedQuadraticBilinear_apply, diskChartedQuadraticBilinear_apply,
    diskChartedEulerField_second_derivative_symmetric]

theorem diskChartedEulerField_fderiv_zero : fderiv ℝ diskChartedEulerField (0 : PeriodicC1HolderHalf) =
    diskRotatingDerivative := by
  with_reducible
    exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      diskChartedEulerField_hasFDerivAt_zero

theorem diskChartedDerivativeLine_hasDerivAt (direction : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => fderiv ℝ diskChartedEulerField (scalar • direction))
      ((2 : ℝ) • diskChartedQuadraticBilinear direction) 0 := by
  have outer : HasFDerivAt (fderiv ℝ diskChartedEulerField)
      (fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf)) 0 := by
    with_reducible
      exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        diskChartedEulerField_eventually_twice_differentiable.self_of_nhds.2
  have line : HasDerivAt (fun scalar : ℝ => scalar • direction) direction 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const direction
  have actual : HasDerivAt (fun scalar : ℝ => fderiv ℝ diskChartedEulerField (scalar • direction))
      (fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) direction) 0 := by
    apply HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ)
      (E := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (x := (0 : ℝ)) outer line
    simp
  have double : (2 : ℝ) • diskChartedQuadraticBilinear direction =
      fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) direction := by
    apply ContinuousLinearMap.ext
    intro value
    change (2 : ℝ) • diskChartedQuadraticBilinear direction value = _
    rw [diskChartedQuadraticBilinear_apply, smul_smul]
    norm_num
  rw [double]
  exact actual

theorem diskChartedDerivativeLine_exists_continuousOn (direction : PeriodicC1HolderHalf) :
    ∃ radius > 0, ContinuousOn (fun scalar : ℝ => fderiv ℝ diskChartedEulerField (scalar • direction))
      (Set.Icc (-radius) radius) := by
  have lineContinuous : Continuous (fun scalar : ℝ => scalar • direction) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight direction).continuous
  have lineLimit : Tendsto (fun scalar : ℝ => scalar • direction) (𝓝 0) (𝓝 (0 : PeriodicC1HolderHalf)) := by
    simpa only [zero_smul] using lineContinuous.tendsto 0
  have nearby : ∀ᶠ scalar in 𝓝 (0 : ℝ),
      ContinuousAt (fun scalar : ℝ => fderiv ℝ diskChartedEulerField (scalar • direction)) scalar := by
    filter_upwards [lineLimit.eventually diskChartedEulerField_eventually_twice_differentiable] with scalar regular
    have actual : ContinuousAt (fderiv ℝ diskChartedEulerField) (scalar • direction) := by
      with_reducible
        exact DifferentiableAt.continuousAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
          (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) regular.2
    exact ContinuousAt.comp (g := fderiv ℝ diskChartedEulerField)
      (f := fun scalar : ℝ => scalar • direction) (x := scalar) actual
      (lineContinuous.continuousAt (x := scalar))
  exact EulerNonuniqueness.General.exists_continuousOn_interval_of_eventually_continuousAt _ nearby

end

end EulerNonuniqueness.Paper
