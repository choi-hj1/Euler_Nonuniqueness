import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

local instance relabeledForcingEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem relabeledDiskForcingPrimitive_hasDerivAt (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (degree : ℕ) {frequency time : ℝ} (nonzero : frequency ≠ 0)
    {amplitude : ℝ → ℂ} {amplitudeDerivative : ℂ}
    (amplitudeEquation : HasDerivAt amplitude amplitudeDerivative time) :
    HasDerivAt (relabeledDiskForcingPrimitive angular degree frequency amplitude)
      (frequency • relabeledDiskDerivative angular
          (relabeledDiskForcingPrimitive angular degree frequency amplitude time) +
        (amplitude time * diskForcingPhase degree frequency time) • relabeledDiskForcingMode angular degree +
        (diskForcingPrimitiveFactor degree frequency * amplitudeDerivative * diskForcingPhase degree frequency time) •
          relabeledDiskForcingMode angular degree) time := by
  let transform := (fixedRelabelEquivalence angular small).toContinuousLinearMap
  have transformed := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) time (ContinuousLinearMap.hasFDerivAt transform)
    (diskForcingPrimitive_hasDerivAt degree nonzero amplitudeEquation)
  have pathEquality : (fun current => transform (diskForcingPrimitive degree frequency amplitude current)) =
      relabeledDiskForcingPrimitive angular degree frequency amplitude := by
    funext current
    exact fixedRelabelEquivalence_forcingPrimitive angular small realValues degree frequency amplitude current
  change HasDerivAt (fun current => transform (diskForcingPrimitive degree frequency amplitude current)) _ time at transformed
  rw [pathEquality] at transformed
  apply HasDerivAt.congr_deriv (𝕜 := ℝ) (F := PeriodicC1HolderHalf)
    (f := relabeledDiskForcingPrimitive angular degree frequency amplitude) (x := time) transformed
  have intertwines := relabeledDiskDerivative_intertwines angular small realValues nearby
  have generator := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf =>
    operator (diskForcingPrimitive degree frequency amplitude time)) intertwines
  change relabeledDiskDerivative angular
      (fixedRelabelEquivalence angular small (diskForcingPrimitive degree frequency amplitude time)) =
    fixedRelabelEquivalence angular small
      (diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time)) at generator
  rw [fixedRelabelEquivalence_forcingPrimitive angular small realValues] at generator
  change transform (frequency • diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time) +
      (amplitude time * diskForcingPhase degree frequency time) • c1Conjugate (diskCircleMode (degree + 1)) +
      (diskForcingPrimitiveFactor degree frequency * amplitudeDerivative * diskForcingPhase degree frequency time) •
        c1Conjugate (diskCircleMode (degree + 1))) = _
  rw [map_add, map_add, map_smul]
  change frequency • fixedRelabelEquivalence angular small
      (diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time)) +
    fixedRelabelEquivalence angular small
      ((amplitude time * diskForcingPhase degree frequency time) • c1Conjugate (diskCircleMode (degree + 1))) +
    fixedRelabelEquivalence angular small
      ((diskForcingPrimitiveFactor degree frequency * amplitudeDerivative * diskForcingPhase degree frequency time) •
        c1Conjugate (diskCircleMode (degree + 1))) = _
  rw [← generator, fixedRelabelEquivalence_complex_smul, fixedRelabelEquivalence_complex_smul,
    fixedRelabelEquivalence_forcingMode angular small realValues]

end

end EulerNonuniqueness.Paper
