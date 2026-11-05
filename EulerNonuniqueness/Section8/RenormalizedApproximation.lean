import EulerNonuniqueness.Section8.RenormalizedIntegrability
import EulerNonuniqueness.Section8.RenormalizedTemporal
import EulerNonuniqueness.Section8.RenormalizedSpatial
import EulerNonuniqueness.Section8.RenormalizedError

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.integrable_renormalized_mollified_initial_test
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {renormalization : ℝ → ℝ} (smooth : ContDiff ℝ 1 renormalization)
    {test : ℝ × Plane → ℝ} (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test) (index : ℕ) :
    Integrable (fun position => renormalization (mollification initial index position) * test (0, position)) := by
  have initialEquality : mollification (omega 0) index = mollification initial index :=
    funext (hypotheses.mollification_initial_trace positive index)
  rw [← initialEquality]
  exact ((smooth.continuous.comp (contDiff_mollification (hypotheses.integrable ⟨le_rfl, positive.le⟩) index).continuous).mul
    (contDiff_spatial_slice testSmooth 0).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_slice testCompact 0).mul_left

theorem TransportAnalyticHypotheses.renormalized_mollification_test_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {test : ℝ × Plane → ℝ} (testAdmissible : ScalarTestOn horizon test) (index : ℕ) :
    let integrand := fun point : ℝ × Plane => renormalization (mollification (omega point.1) index point.2) *
      (timeDerivative test point + spatialDerivative test point (biotSavart (omega point.1) point.2))
    let error := fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
      transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2 * test point
    Integrable integrand (spacetimeMeasure horizon) ∧
      Integrable (fun position => renormalization (mollification initial index position) * test (0, position)) ∧
      (∫ point, integrand point ∂spacetimeMeasure horizon) +
        (∫ position, renormalization (mollification initial index position) * test (0, position)) =
          -(∫ point, error point ∂spacetimeMeasure horizon) := by
  let temporal := fun point : ℝ × Plane => renormalization (mollification (omega point.1) index point.2) * timeDerivative test point
  let spatial := fun point : ℝ × Plane => renormalization (mollification (omega point.1) index point.2) *
    spatialDerivative test point (biotSavart (omega point.1) point.2)
  let advective := fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
    fderiv ℝ (mollification (omega point.1) index) point.2 (biotSavart (omega point.1) point.2) * test point
  let error := fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
    transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2 * test point
  let initialTerm := fun position => renormalization (mollification initial index position) * test (0, position)
  obtain ⟨temporalIntegrable, spatialIntegrable, advectiveIntegrable⟩ :=
    hypotheses.renormalized_mollification_integrable_terms positive.le admissible.1 testAdmissible.1 testAdmissible.2.1 index
  have errorIntegrable := hypotheses.integrable_renormalized_commutator_error positive.le admissible
    testAdmissible.1 testAdmissible.2.1 index
  have initialIntegrable := hypotheses.integrable_renormalized_mollified_initial_test positive admissible.1
    testAdmissible.1 testAdmissible.2.1 index
  have combinedIntegrable : Integrable (fun point => temporal point + (error point - advective point))
      (spacetimeMeasure horizon) := temporalIntegrable.add (errorIntegrable.sub advectiveIntegrable)
  have temporalIdentity (position : Plane) :
      (∫ time in Ioo 0 horizon, temporal (time, position) + (error (time, position) - advective (time, position))) =
        -initialTerm position := by
    have identity := hypotheses.renormalized_temporal_test_identity positive admissible.1 testAdmissible index position
    have integrandEquality : (fun time => temporal (time, position) + (error (time, position) - advective (time, position))) =
        (fun time => renormalization (mollification (omega time) index position) * timeDerivative test (time, position) +
          deriv renormalization (mollification (omega time) index position) *
            (transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega time)) (omega time) position -
              fderiv ℝ (mollification (omega time) index) position (biotSavart (omega time) position)) * test (time, position)) := by
      funext time
      dsimp [temporal, error, advective]
      ring
    rw [integrandEquality]
    change _ = -(renormalization (mollification initial index position) * test (0, position))
    linarith
  have integratedTemporal : (∫ point, temporal point ∂spacetimeMeasure horizon) +
      (∫ point, error point ∂spacetimeMeasure horizon) - (∫ point, advective point ∂spacetimeMeasure horizon) +
        (∫ position, initialTerm position) = 0 := by
    have identity := integral_prod_symm _ combinedIntegrable
    change (∫ point, temporal point + (error point - advective point) ∂spacetimeMeasure horizon) = _ at identity
    rw [show (∫ position, ∫ time in Ioo 0 horizon,
        temporal (time, position) + (error (time, position) - advective (time, position))) =
        -(∫ position, initialTerm position) by simp_rw [temporalIdentity]; rw [integral_neg]] at identity
    have addition := integral_add (f := temporal) (g := fun point => error point - advective point)
      temporalIntegrable (errorIntegrable.sub advectiveIntegrable)
    have subtraction := integral_sub (f := error) (g := advective) errorIntegrable advectiveIntegrable
    rw [addition, subtraction] at identity
    linarith
  have spatialIdentity : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon),
      (∫ position, spatial (time, position)) + (∫ position, advective (time, position)) = 0 := by
    obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    have identity := (integral_renormalized_spatial_transport (hypotheses.integrable closedInside)
      (hypotheses.membership 4 (by norm_num) time closedInside) radiusPositive.le (supported time closedInside)
      ((contDiff_mollification (hypotheses.integrable closedInside) index).of_le (by simp)) admissible.1
      ((contDiff_spatial_slice testAdmissible.1 time).of_le (by simp))
      (hasCompactSupport_spatial_slice testAdmissible.2.1 time)).2.2
    simpa only [spatial, advective, fderiv_spatial_slice testAdmissible.1] using identity
  have integratedSpatial : (∫ point, spatial point ∂spacetimeMeasure horizon) +
      (∫ point, advective point ∂spacetimeMeasure horizon) = 0 := by
    change (∫ point, spatial point ∂((volume.restrict (Ioo 0 horizon)).prod volume)) +
      (∫ point, advective point ∂((volume.restrict (Ioo 0 horizon)).prod volume)) = 0
    rw [integral_prod spatial spatialIntegrable, integral_prod advective advectiveIntegrable]
    exact (integral_add spatialIntegrable.integral_prod_left advectiveIntegrable.integral_prod_left).symm.trans
      (integral_eq_zero_of_ae spatialIdentity)
  have integrandEquality : (fun point : ℝ × Plane => renormalization (mollification (omega point.1) index point.2) *
      (timeDerivative test point + spatialDerivative test point (biotSavart (omega point.1) point.2))) =
      (fun point => temporal point + spatial point) := by funext point; dsimp [temporal, spatial]; ring
  dsimp only
  rw [integrandEquality]
  refine ⟨temporalIntegrable.add spatialIntegrable, initialIntegrable, ?_⟩
  rw [integral_add temporalIntegrable spatialIntegrable]
  linarith

end EulerNonuniqueness
