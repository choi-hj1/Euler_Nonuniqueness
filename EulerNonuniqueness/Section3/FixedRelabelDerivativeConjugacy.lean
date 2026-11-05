import EulerNonuniqueness.Section3.FixedRelabelVelocityEquivariance
import EulerNonuniqueness.Section3.ContourVelocityFrechet
import EulerNonuniqueness.Section3.DiskRotatingDerivative

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabelDerivativeConjugacyRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

local instance relabelDerivativeConjugacyOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourVelocity_derivative_fixedRelabelEquivalence (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ <
      min 1 (2 / (3 * Real.pi))) :
    (fderiv ℝ extendedContourVelocity (fixedRelabelEquivalence angular angularSmall data)).comp
      (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap =
    (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.comp
      (fderiv ℝ extendedContourVelocity data) := by
  let relabel := (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap
  have firstDerivative : HasFDerivAt extendedContourVelocity (fderiv ℝ extendedContourVelocity (relabel data)) (relabel data) :=
    DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (differentiableAt_extendedContourVelocity (relabel data) composedSmall)
  have secondDerivative : HasFDerivAt extendedContourVelocity (fderiv ℝ extendedContourVelocity data) data :=
    DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (differentiableAt_extendedContourVelocity data small)
  have relabelDerivative (point : PeriodicC1HolderHalf) : HasFDerivAt relabel relabel point := by
    with_reducible
      exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) relabel
  have left : HasFDerivAt (fun current => extendedContourVelocity (relabel current))
      ((fderiv ℝ extendedContourVelocity (relabel data)).comp relabel) data := by
    with_reducible
      simpa only [Function.comp_def] using HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
        (G := PeriodicC1HolderHalf) (f := fun current => relabel current) (g := extendedContourVelocity)
        data firstDerivative (relabelDerivative data)
  have right : HasFDerivAt (fun current => relabel (extendedContourVelocity current))
      (relabel.comp (fderiv ℝ extendedContourVelocity data)) data := by
    with_reducible
      simpa only [Function.comp_def] using HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
        (G := PeriodicC1HolderHalf) (f := extendedContourVelocity) (g := fun current => relabel current)
        data (relabelDerivative (extendedContourVelocity data)) secondDerivative
  have firstNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have distanceNeighborhood : ∀ᶠ current in 𝓝 data,
        dist current standardCircleBanach < min 1 (2 / (3 * Real.pi)) :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds
        (by
          change dist data standardCircleBanach < min 1 (2 / (3 * Real.pi))
          rw [dist_eq_norm data standardCircleBanach]
          exact small)
    filter_upwards [distanceNeighborhood] with current close
    exact (dist_eq_norm current standardCircleBanach) ▸ close
  have secondNeighborhood : ∀ᶠ current in 𝓝 data,
      ‖relabel current - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have distanceNeighborhood : ∀ᶠ current in 𝓝 data,
        dist (relabel current) standardCircleBanach < min 1 (2 / (3 * Real.pi)) :=
      (isOpen_lt (relabel.continuous.dist continuous_const) continuous_const).mem_nhds
        (by
          change dist (relabel data) standardCircleBanach < min 1 (2 / (3 * Real.pi))
          rw [dist_eq_norm (relabel data) standardCircleBanach]
          exact composedSmall)
    filter_upwards [distanceNeighborhood] with current close
    exact (dist_eq_norm (relabel current) standardCircleBanach) ▸ close
  have equality : (fun current => extendedContourVelocity (relabel current)) =ᶠ[𝓝 data]
      (fun current => relabel (extendedContourVelocity current)) := by
    filter_upwards [firstNeighborhood, secondNeighborhood] with current first second
    exact extendedContourVelocity_fixedRelabelEquivalence angular angularSmall current first second
  have rightAtLeft : HasFDerivAt (fun current => extendedContourVelocity (relabel current))
      (relabel.comp (fderiv ℝ extendedContourVelocity data)) data := by
    with_reducible
      exact HasFDerivAt.congr_of_eventuallyEq (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) right equality
  with_reducible
    exact HasFDerivAt.unique (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) left rightAtLeft

def relabeledDiskDerivative (angular : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ extendedContourVelocity (diskRelabelCurve angular 1) - c1ProductCLM (c1Constant (Complex.I / 2))

theorem relabeledDiskDerivative_apply (angular direction : PeriodicC1HolderHalf) :
    relabeledDiskDerivative angular direction =
      fderiv ℝ extendedContourVelocity (diskRelabelCurve angular 1) direction - (Complex.I / 2) • direction := by
  change fderiv ℝ extendedContourVelocity (diskRelabelCurve angular 1) direction -
    c1Product (c1Constant (Complex.I / 2)) direction = _
  congr 1
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem relabeledDiskDerivative_zero : relabeledDiskDerivative 0 = diskRotatingDerivative := by
  have circle : diskRelabelCurve 0 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  unfold relabeledDiskDerivative
  rw [circle]
  rfl

theorem relabeledDiskDerivative_intertwines (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (composedSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (relabeledDiskDerivative angular).comp (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap =
      (fixedRelabelEquivalence angular angularSmall).toContinuousLinearMap.comp diskRotatingDerivative := by
  have circleSmall : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rw [sub_self standardCircleBanach, norm_zero]
    positivity
  have derivative := contourVelocity_derivative_fixedRelabelEquivalence angular angularSmall standardCircleBanach
    circleSmall (by simpa only [fixedRelabelEquivalence_circle angular angularSmall realValues] using composedSmall)
  rw [fixedRelabelEquivalence_circle angular angularSmall realValues] at derivative
  apply ContinuousLinearMap.ext
  intro direction
  have derivativeValue := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => operator direction) derivative
  change fderiv ℝ extendedContourVelocity (diskRelabelCurve angular 1)
    (fixedRelabelEquivalence angular angularSmall direction) =
      fixedRelabelEquivalence angular angularSmall (fderiv ℝ extendedContourVelocity standardCircleBanach direction) at derivativeValue
  change relabeledDiskDerivative angular (fixedRelabelEquivalence angular angularSmall direction) =
    fixedRelabelEquivalence angular angularSmall (diskRotatingDerivative direction)
  rw [relabeledDiskDerivative_apply, diskRotatingDerivative_apply, derivativeValue]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

end EulerNonuniqueness.Paper
