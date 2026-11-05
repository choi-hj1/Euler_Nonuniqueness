import EulerNonuniqueness.Section3.CentroidStrainProjectionJet
import EulerNonuniqueness.Section3.ContourCentroidRelativeConstraint

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] complexStrainGaugeC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

def projectedComplexStrainTaylorRemainder (base : PeriodicC1HolderHalf) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  contourCentroidGaugeProjection (base + direction) (coefficient • c1Conjugate (base + direction)) -
    contourCentroidGaugeProjection base (coefficient • c1Conjugate base) -
    fderiv ℝ (fun current : PeriodicC1HolderHalf =>
      contourCentroidGaugeProjection current (coefficient • c1Conjugate current)) base direction

theorem projectedComplexStrainTaylorRemainder_eq_centroid_defect
    (base direction : PeriodicC1HolderHalf) (coefficient : ℂ)
    (small : ‖base - standardCircleBanach‖ < 1 / 3)
    (nextSmall : ‖base + direction - standardCircleBanach‖ < 1 / 3)
    (centered : contourCentroidFunctional (base + direction) = contourCentroidFunctional base) :
    projectedComplexStrainTaylorRemainder base coefficient direction =
      coefficient • c1Constant (star (fderiv ℝ contourCentroidFunctional base direction)) := by
  unfold projectedComplexStrainTaylorRemainder
  rw [contourCentroidGaugeProjection_complex_strain _ coefficient nextSmall,
    contourCentroidGaugeProjection_complex_strain _ coefficient small,
    projected_complex_strain_derivative_projection base direction coefficient small]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (coefficient * (star (base.val.1 label + direction.val.1 label) -
      star (contourCentroidFunctional (base + direction))) -
    coefficient * (star (base.val.1 label) - star (contourCentroidFunctional base))) -
    coefficient * star (direction.val.1 label - fderiv ℝ contourCentroidFunctional base direction) =
      coefficient * star (fderiv ℝ contourCentroidFunctional base direction)
  rw [centered, star_add, star_sub]
  ring

theorem projectedComplexStrainTaylorRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initialBase finalBase initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      contourCentroidFunctional (initialBase + initialIncrement) = contourCentroidFunctional initialBase →
      contourCentroidFunctional (finalBase + finalIncrement) = contourCentroidFunctional finalBase →
      ∀ coefficient : ℂ,
      ‖projectedComplexStrainTaylorRemainder initialBase coefficient initialIncrement -
        projectedComplexStrainTaylorRemainder finalBase coefficient finalIncrement‖ ≤
      ‖coefficient‖ * (constant : ℝ) *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) := by
  obtain ⟨radius, positive, constant, bound⟩ :=
    contourCentroidDerivative_exists_relative_quadratic_constraint_ball
  refine ⟨min radius (1 / 6), lt_min positive (by norm_num), constant, ?_⟩
  intro initialBase finalBase initialIncrement finalIncrement initialInside finalInside initialCentroid finalCentroid coefficient
  have initialBudget := initialInside.trans (min_le_right radius (1 / 6))
  have finalBudget := finalInside.trans (min_le_right radius (1 / 6))
  have initialSmall : ‖initialBase - standardCircleBanach‖ < 1 / 3 := by
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have finalSmall : ‖finalBase - standardCircleBanach‖ < 1 / 3 := by
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have initialNext : ‖initialBase + initialIncrement - standardCircleBanach‖ < 1 / 3 := by
    have triangle : ‖initialBase + initialIncrement - standardCircleBanach‖ ≤
        ‖initialBase - standardCircleBanach‖ + ‖initialIncrement‖ := by
      convert norm_add_le (initialBase - standardCircleBanach) initialIncrement using 1 <;> congr 1 <;> abel
    linarith [norm_nonneg finalIncrement]
  have finalNext : ‖finalBase + finalIncrement - standardCircleBanach‖ < 1 / 3 := by
    have triangle : ‖finalBase + finalIncrement - standardCircleBanach‖ ≤
        ‖finalBase - standardCircleBanach‖ + ‖finalIncrement‖ := by
      convert norm_add_le (finalBase - standardCircleBanach) finalIncrement using 1 <;> congr 1 <;> abel
    linarith [norm_nonneg initialIncrement]
  rw [projectedComplexStrainTaylorRemainder_eq_centroid_defect initialBase initialIncrement coefficient
      initialSmall initialNext initialCentroid,
    projectedComplexStrainTaylorRemainder_eq_centroid_defect finalBase finalIncrement coefficient
      finalSmall finalNext finalCentroid, ← smul_sub, norm_smul]
  have constants (first second : ℂ) : c1Constant (star first) - c1Constant (star second) =
      c1Constant (star (first - second)) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    exact (star_sub first second).symm
  rw [constants]
  have estimate := bound initialBase finalBase initialIncrement finalIncrement
    (initialInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _)) initialCentroid finalCentroid
  have normBound : ‖c1Constant (star
      (fderiv ℝ contourCentroidFunctional initialBase initialIncrement -
        fderiv ℝ contourCentroidFunctional finalBase finalIncrement))‖ ≤ (constant : ℝ) *
      ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
        ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 2) :=
    (c1Constant_norm_bound _).trans (by simpa only [norm_star] using estimate)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left normBound (norm_nonneg coefficient)

end EulerNonuniqueness.Paper
