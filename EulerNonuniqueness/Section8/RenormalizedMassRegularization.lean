import EulerNonuniqueness.Section8.RenormalizedSpatial
import EulerNonuniqueness.Section8.RegularizedBounds
import EulerNonuniqueness.Section8.RegularizedMeasurability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem tsupport_mollification_subset {vorticity : Vorticity} {radius : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius) (index : ℕ) :
    tsupport (mollification vorticity index) ⊆ Metric.closedBall 0 (radius + 1) :=
  closure_minimal (support_mollification supported index) Metric.isClosed_closedBall

theorem integral_renormalized_mollified_advection_eq_zero
    {vorticity : Vorticity} {radius : ℝ} (radiusPositive : 0 < radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {renormalization : ℝ → ℝ} (smooth : ContDiff ℝ 1 renormalization) (zero : renormalization 0 = 0)
    (index : ℕ) :
    Integrable (fun position => deriv renormalization (mollification vorticity index position) *
      fderiv ℝ (mollification vorticity index) position (biotSavart vorticity position)) ∧
      (∫ position, deriv renormalization (mollification vorticity index position) *
        fderiv ℝ (mollification vorticity index) position (biotSavart vorticity position)) = 0 := by
  have integrable : Integrable vorticity := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have regularizedSmooth := contDiff_mollification integrable index
  have velocityContinuous := continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (membership 4 (by norm_num)) (by norm_num) radiusPositive.le supported
  let cutoff : ContDiffBump (0 : Plane) := ⟨radius + 2, radius + 3, by linarith, by linarith⟩
  have cutoffOne (position : Plane) (inside : position ∈ Metric.closedBall (0 : Plane) (radius + 1)) : cutoff position = 1 := by
    apply cutoff.one_of_mem_closedBall
    exact Metric.closedBall_subset_closedBall (by change radius + 1 ≤ radius + 2; linarith) inside
  have cutoffDerivativeZero (position : Plane) (inside : position ∈ Metric.closedBall (0 : Plane) (radius + 1)) :
      fderiv ℝ cutoff position = 0 := by
    have interior : position ∈ Metric.ball (0 : Plane) cutoff.rIn := by
      have normBound : ‖position‖ ≤ radius + 1 := by simpa using inside
      change dist position 0 < radius + 2
      simpa using lt_of_le_of_lt normBound (by linarith : radius + 1 < radius + 2)
    have equality := (cutoff.eventuallyEq_one_of_mem_ball interior).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ cutoff position = fderiv ℝ (fun _ : Plane => (1 : ℝ)) position at equality
    simpa only [fderiv_const] using equality
  have derivativeSupported := tsupport_mollification_subset supported index
  have advectiveContinuous : Continuous (fun position => deriv renormalization (mollification vorticity index position) *
      fderiv ℝ (mollification vorticity index) position (biotSavart vorticity position)) :=
    ((smooth.continuous_deriv le_rfl).comp regularizedSmooth.continuous).mul
      ((regularizedSmooth.continuous_fderiv (by simp)).clm_apply velocityContinuous)
  have advectiveCompact : HasCompactSupport (fun position => deriv renormalization (mollification vorticity index position) *
      fderiv ℝ (mollification vorticity index) position (biotSavart vorticity position)) := by
    apply (hasCompactSupport_mollification supported index).mono'
    intro position nonzero
    by_contra outside
    have derivativeZero := fderiv_of_not_mem_tsupport (𝕜 := ℝ) outside
    exact nonzero (by simp [derivativeZero])
  have advectiveIntegrable := advectiveContinuous.integrable_of_hasCompactSupport advectiveCompact (μ := volume)
  have identity := (integral_renormalized_spatial_transport integrable (membership 4 (by norm_num)) radiusPositive.le supported
    (regularizedSmooth.of_le (by simp)) smooth cutoff.contDiff cutoff.hasCompactSupport).2.2
  have firstZero : (fun position => renormalization (mollification vorticity index position) *
      fderiv ℝ cutoff position (biotSavart vorticity position)) = 0 := by
    funext position
    by_cases regularizedZero : mollification vorticity index position = 0
    · simp only [regularizedZero, zero, zero_mul, Pi.zero_apply]
    · have inside := derivativeSupported (subset_tsupport _ regularizedZero)
      simp only [cutoffDerivativeZero position inside, ContinuousLinearMap.zero_apply, mul_zero, Pi.zero_apply]
  have cutoffEquality : (fun position => deriv renormalization (mollification vorticity index position) *
      fderiv ℝ (mollification vorticity index) position (biotSavart vorticity position) * cutoff position) =
      (fun position => deriv renormalization (mollification vorticity index position) *
        fderiv ℝ (mollification vorticity index) position (biotSavart vorticity position)) := by
    funext position
    by_cases inside : position ∈ tsupport (mollification vorticity index)
    · rw [cutoffOne position (derivativeSupported inside), mul_one]
    · simp only [fderiv_of_not_mem_tsupport (𝕜 := ℝ) inside, ContinuousLinearMap.zero_apply, mul_zero, zero_mul]
  rw [firstZero, integral_zero', zero_add, cutoffEquality] at identity
  exact ⟨advectiveIntegrable, identity⟩

theorem TransportAnalyticHypotheses.integrable_renormalized_mollified_advection
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization) (index : ℕ) :
    Integrable (fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
      fderiv ℝ (mollification (omega point.1) index) point.2 (biotSavart (omega point.1) point.2)) (spacetimeMeasure horizon) := by
  obtain ⟨radius, positive, supported⟩ := hypotheses.supported
  obtain ⟨derivativeBound, derivativeNonnegative, derivativeBounded⟩ := admissible.2
  obtain ⟨regularizedBound, regularizedNonnegative, regularizedBounded⟩ := hypotheses.uniform_mollification_bound index
  obtain ⟨velocityBound, velocityFinite, velocityBounded⟩ := hypotheses.uniform_biotSavart_bound_on_closedBall
    (show 0 ≤ radius + 1 by linarith)
  have regularizedMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2) nonnegative (hypotheses.measurable_mollification index)
  have advectiveMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => fderiv ℝ (mollification (omega point.1) index) point.2 (biotSavart (omega point.1) point.2))
    nonnegative (hypotheses.measurable_mollification_advectiveDerivative index)
  apply integrable_spacetime_of_supported_bounded
    (((admissible.1.continuous_deriv le_rfl).comp_aestronglyMeasurable regularizedMeasurable).mul advectiveMeasurable)
    (radius := radius + 1) (bound := derivativeBound * (regularizedBound * velocityBound.toReal))
  · intro time inside position positionInside
    simp only [Pi.mul_apply]
    rw [norm_mul]
    have velocityEstimate := ENNReal.toReal_mono velocityFinite.ne
      (velocityBounded time ⟨inside.1.le, inside.2.le⟩ position positionInside)
    simp only [ENNReal.toReal_ofReal (norm_nonneg _)] at velocityEstimate
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using derivativeBounded _)
      (((regularizedBounded time ⟨inside.1.le, inside.2.le⟩ position).2 _).trans
        (mul_le_mul_of_nonneg_left velocityEstimate regularizedNonnegative)) (norm_nonneg _) derivativeNonnegative
  · intro time inside position outside
    have outsideSupport : position ∉ tsupport (mollification (omega time) index) :=
      fun member => outside (tsupport_mollification_subset (supported time ⟨inside.1.le, inside.2.le⟩) index member)
    simp only [Pi.mul_apply, fderiv_of_not_mem_tsupport (𝕜 := ℝ) outsideSupport, ContinuousLinearMap.zero_apply, mul_zero]

end EulerNonuniqueness
