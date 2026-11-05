import EulerNonuniqueness.Section3.IndependentForcingFourierSelection
import EulerNonuniqueness.Section3.PeriodicHilbertProjectionFourier

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentResonanceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

local instance independentResonancePositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem independentStrainForcing_resonant_block_zero (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule)
    (positiveInput : ∀ degree : ℤ, degree ≤ 1 → periodicC1FourierCoefficient data degree = 0) :
    periodicHilbertNegativeProjection (independentForcingRadialBlock 0 data) = 0 := by
  apply periodicHilbertNegativeProjection_eq_zero_of_negative_coefficients
  intro degree negative
  exact independentStrainForcing_negative_fourier_zero data member positiveInput degree negative

theorem independentStrainForcing_resonant_positive_input (data : PeriodicC1HolderHalf)
    (member : periodicHilbertPositiveProjection data ∈ contourContinuousVectorSubmodule)
    (firstMode : periodicC1FourierCoefficient data 1 = 0) :
    periodicHilbertNegativeProjection
      (independentForcingRadialBlock 0 (periodicHilbertPositiveProjection data)) = 0 := by
  apply independentStrainForcing_resonant_block_zero _ member
  intro degree upper
  by_cases nonpositive : degree ≤ 0
  · exact periodicHilbertPositiveProjection_fourier_nonpositive_zero data degree nonpositive
  · have one : degree = 1 := by omega
    subst degree
    rw [periodicHilbertPositiveProjection_fourier_one, firstMode]

end

end EulerNonuniqueness.Paper
