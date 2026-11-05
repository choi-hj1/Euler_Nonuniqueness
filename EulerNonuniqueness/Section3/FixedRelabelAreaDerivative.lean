import EulerNonuniqueness.Section3.FixedRelabelArea
import EulerNonuniqueness.Section3.DiskSpectralFiberAlgebra
import EulerNonuniqueness.Section3.DiskAreaDerivative
import EulerNonuniqueness.General.LinearInvariantDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem contourAreaFunctional_fderiv_fixedRelabel (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) :
    (fderiv ℝ contourAreaFunctional (fixedRelabelEquivalence angular small data)).comp
      (fixedRelabelEquivalence angular small).toContinuousLinearMap = fderiv ℝ contourAreaFunctional data := by
  let relabel := (fixedRelabelEquivalence angular small).toContinuousLinearMap
  change (fderiv ℝ contourAreaFunctional (relabel data)).comp relabel = fderiv ℝ contourAreaFunctional data
  have regular := (analyticAt_contourAreaFunctional (relabel data)).differentiableAt
  have invariant := contourAreaFunctional_fixedRelabel angular small
  with_reducible
    exact EulerNonuniqueness.General.fderiv_comp_eq_of_linear_invariant
      (Space := PeriodicC1HolderHalf) (Target := ℝ) contourAreaFunctional relabel data regular invariant

theorem diskRadialMeanCLM_rotatingDerivative_zero (direction : PeriodicC1HolderHalf) :
    diskRadialMeanCLM (diskRotatingDerivative direction) = 0 := by
  have radial := congrArg Prod.fst (diskPhysicalCoordinates_generator direction)
  rw [diskLinearGenerator_apply] at radial
  change diskRadialPart (diskRotatingDerivative direction) =
    (-1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart direction) at radial
  change ((periodicMeanProjectionCCLM (diskRadialPart (diskRotatingDerivative direction))).val.1 0).re = 0
  rw [radial]
  have scalar : periodicMeanProjectionCCLM ((-1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart direction)) =
      (-1 / 2 : ℝ) • periodicMeanProjectionCCLM (periodicHilbertC1 (diskRadialPart direction)) :=
    periodicMeanProjectionCCLM.toLinearMap.map_smul_of_tower _ _
  rw [scalar, periodicMeanProjectionCCLM_hilbert]
  change (((-1 / 2 : ℝ) • (0 : ℂ)).re) = 0
  simp

theorem contourAreaFunctional_fderiv_circle_rotatingDerivative_zero (direction : PeriodicC1HolderHalf) :
    fderiv ℝ contourAreaFunctional standardCircleBanach (diskRotatingDerivative direction) = 0 := by
  have derivative : fderiv ℝ contourAreaFunctional standardCircleBanach = (2 * Real.pi) • diskRadialMeanCLM := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := ℝ) hasFDerivAt_contourAreaFunctional_circle
  rw [derivative]
  change (2 * Real.pi) • diskRadialMeanCLM (diskRotatingDerivative direction) = 0
  rw [diskRadialMeanCLM_rotatingDerivative_zero, smul_zero]

theorem contourAreaFunctional_fderiv_relabel_rotatingDerivative_zero
    (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (composedSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (direction : PeriodicC1HolderHalf) :
    fderiv ℝ contourAreaFunctional (diskRelabelCurve angular 1) (relabeledDiskDerivative angular direction) = 0 := by
  let relabel := fixedRelabelEquivalence angular small
  obtain ⟨point, pointIdentity⟩ := relabel.surjective direction
  have intertwines := relabeledDiskDerivative_intertwines angular small realValues composedSmall
  have evaluated := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear point) intertwines
  change relabeledDiskDerivative angular (relabel point) = relabel (diskRotatingDerivative point) at evaluated
  rw [← pointIdentity, evaluated]
  have areaDerivative := contourAreaFunctional_fderiv_fixedRelabel angular small standardCircleBanach
  rw [fixedRelabelEquivalence_circle angular small realValues] at areaDerivative
  have actual := congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] ℝ => linear (diskRotatingDerivative point)) areaDerivative
  change fderiv ℝ contourAreaFunctional (diskRelabelCurve angular 1) (relabel (diskRotatingDerivative point)) =
    fderiv ℝ contourAreaFunctional standardCircleBanach (diskRotatingDerivative point) at actual
  rw [actual]
  exact contourAreaFunctional_fderiv_circle_rotatingDerivative_zero point

end

end EulerNonuniqueness.Paper
