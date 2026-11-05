import EulerNonuniqueness.Section8.StreamCurlPairing
import EulerNonuniqueness.Section8.TestPairingDerivative
import EulerNonuniqueness.Section8.VelocityContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem integral_biotSavart_timeDerivative_eq_neg_vorticity_stream {vorticity : Vorticity} {radius : ℝ}
    (nonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (time : ℝ) :
    Integrable (fun position => ⟪biotSavart vorticity position, timeDerivative test (time, position)⟫_ℝ) ∧
      (∫ position, ⟪biotSavart vorticity position, timeDerivative test (time, position)⟫_ℝ) =
        -(∫ position, vorticity position * timeDerivative (streamFunction test) (time, position)) := by
  have sourceIntegrable : Integrable vorticity := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have velocityContinuous := continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (membership 4 (by norm_num)) (by norm_num) nonnegative supported
  obtain ⟨observationRadius, positive, bounded⟩ :=
    (compact.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  let cutoff : ContDiffBump (0 : Plane) := ⟨observationRadius + 1, observationRadius + 2, by linarith, by linarith⟩
  let weight := fun position => cutoff position • biotSavart vorticity position
  have weightIntegrable : Integrable weight := (cutoff.continuous.smul velocityContinuous).integrable_of_hasCompactSupport
    cutoff.hasCompactSupport.smul_right
  have cutoffOne (other : ℝ) (position : Plane) (inside : (other, position) ∈ tsupport test) : cutoff position = 1 := by
    apply cutoff.one_of_mem_closedBall
    have bound := bounded position ⟨(other, position), inside, rfl⟩
    change dist position 0 ≤ observationRadius + 1
    rw [dist_zero_right]
    linarith
  have pairingEquality (other : ℝ) : (fun position => ⟪weight position, test (other, position)⟫_ℝ) =
      (fun position => ⟪biotSavart vorticity position, test (other, position)⟫_ℝ) := by
    funext position
    by_cases inside : (other, position) ∈ tsupport test
    · simp only [weight, cutoffOne other position inside, one_smul]
    · simp only [image_eq_zero_of_nmem_tsupport inside, inner_zero_right]
  have derivativePairingEquality : (fun position => ⟪weight position, timeDerivative test (time, position)⟫_ℝ) =
      (fun position => ⟪biotSavart vorticity position, timeDerivative test (time, position)⟫_ℝ) := by
    funext position
    by_cases inside : (time, position) ∈ tsupport test
    · simp only [weight, cutoffOne time position inside, one_smul]
    · simp only [timeDerivative, fderiv_of_not_mem_tsupport (𝕜 := ℝ) inside, ContinuousLinearMap.zero_apply, inner_zero_right]
  have potentialSmooth := contDiff_streamFunction smooth compact
  have potentialCompact := hasCompactSupport_streamFunction smooth compact divergence
  have functionEquality : (fun other => ∫ position, ⟪weight position, test (other, position)⟫_ℝ) =
      (fun other => -(∫ position, vorticity position * streamFunction test (other, position))) := by
    funext other
    rw [pairingEquality]
    exact (integral_biotSavart_vectorTest_eq_neg_vorticity_stream sourceIntegrable supported smooth compact divergence other).2
  have vectorDerivative := hasDerivAt_integral_test_pairing weightIntegrable smooth compact time
  have scalarDerivative := hasDerivAt_integral_test_pairing sourceIntegrable potentialSmooth potentialCompact time
  have scalarDerivative' : HasDerivAt (fun other => ∫ position, vorticity position * streamFunction test (other, position))
      (∫ position, vorticity position * timeDerivative (streamFunction test) (time, position)) time := by
    simpa only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using scalarDerivative.2
  have derivative := vectorDerivative.2
  rw [functionEquality] at derivative
  have equality := derivative.unique scalarDerivative'.neg
  rw [derivativePairingEquality] at equality
  exact ⟨derivativePairingEquality ▸ vectorDerivative.1, equality⟩

end EulerNonuniqueness
