import EulerNonuniqueness.Section8.StreamMomentumSpatial
import EulerNonuniqueness.Section8.StreamMomentumTemporal
import EulerNonuniqueness.Section8.MomentumIntegrability
import EulerNonuniqueness.Section8.InitialAETrace

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.weakMomentumOn
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon) :
    WeakMomentumOn horizon (biotSavart initial) (fun time => biotSavart (omega time)) := by
  intro test admissible
  let potential := streamFunction test
  have potentialAdmissible : ScalarTestOn horizon potential := scalarTestOn_streamFunction admissible
  have scalarTransport := hypotheses.weakTransport potential potentialAdmissible
  let scalarField := fun point : ℝ × Plane => omega point.1 point.2 *
    (timeDerivative potential point + spatialDerivative potential point (biotSavart (omega point.1) point.2))
  let momentumField := fun point : ℝ × Plane => ⟪biotSavart (omega point.1) point.2,
    timeDerivative test point + spatialDerivative test point (biotSavart (omega point.1) point.2)⟫_ℝ
  change Integrable scalarField (spacetimeMeasure horizon) ∧
    Integrable (fun position => initial position * potential (0, position)) ∧
    (∫ point, scalarField point ∂spacetimeMeasure horizon) + (∫ position, initial position * potential (0, position)) = 0 at scalarTransport
  obtain ⟨temporalIntegrable, spatialIntegrable⟩ := hypotheses.integrable_momentum_terms positive.le admissible.1 admissible.2.1
  have momentumIntegrable : Integrable momentumField (spacetimeMeasure horizon) := by
    simpa only [momentumField, inner_add_right] using temporalIntegrable.add spatialIntegrable
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  have potentialTemporalSmooth : ContDiff ℝ ∞ (fun point => timeDerivative potential point) :=
    (potentialAdmissible.1.fderiv_right (by simp)).clm_apply contDiff_const
  have potentialTemporalCompact : HasCompactSupport (fun point => timeDerivative potential point) :=
    potentialAdmissible.2.1.fderiv_apply ℝ (1, 0)
  have slicesEqual : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon),
      (∫ position, momentumField (time, position)) = -(∫ position, scalarField (time, position)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, temporalIntegrable.prod_right_ae, spatialIntegrable.prod_right_ae]
      with time inside temporalSlice spatialSlice
    have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    have membership := fun exponent bound => hypotheses.membership exponent bound time closedInside
    have temporalEquality := (integral_biotSavart_timeDerivative_eq_neg_vorticity_stream radiusPositive.le
      membership (supported time closedInside) admissible.1 admissible.2.1 admissible.2.2.2 time).2
    have spatialEquality := integral_vorticity_stream_transport_eq_neg_momentum radiusPositive.le membership
      (supported time closedInside) admissible.1 admissible.2.1 admissible.2.2.2 time
    have scalarTemporalIntegrable := hypotheses.integrable_smooth_moment closedInside
      (contDiff_spatial_slice potentialTemporalSmooth time) (hasCompactSupport_spatial_slice potentialTemporalCompact time)
    have scalarSpatialIntegrable := hypotheses.integrable_transportFlux closedInside
      (contDiff_spatial_slice potentialAdmissible.1 time) (hasCompactSupport_spatial_slice potentialAdmissible.2.1 time)
    simp_rw [fderiv_spatial_slice potentialAdmissible.1] at scalarSpatialIntegrable
    dsimp only [momentumField, scalarField]
    simp_rw [inner_add_right, mul_add]
    rw [integral_add temporalSlice spatialSlice, integral_add scalarTemporalIntegrable scalarSpatialIntegrable]
    change _ = -((∫ position, omega time position * timeDerivative (streamFunction test) (time, position)) +
      ∫ position, omega time position * spatialDerivative (streamFunction test) (time, position) (biotSavart (omega time) position))
    linarith
  have totalEquality : (∫ point, momentumField point ∂spacetimeMeasure horizon) =
      -(∫ point, scalarField point ∂spacetimeMeasure horizon) := by
    have momentumFubini := integral_prod momentumField momentumIntegrable
    have scalarFubini := integral_prod scalarField scalarTransport.1
    change (∫ point, momentumField point ∂spacetimeMeasure horizon) = _ at momentumFubini
    change (∫ point, scalarField point ∂spacetimeMeasure horizon) = _ at scalarFubini
    rw [momentumFubini, scalarFubini, ← integral_neg]
    exact integral_congr_ae slicesEqual
  have initialEquality := hypotheses.initial_ae_eq positive
  have initialVelocityEquality := biotSavart_congr_ae initialEquality
  have initialCurl := integral_biotSavart_vectorTest_eq_neg_vorticity_stream
    (hypotheses.integrable ⟨le_rfl, positive.le⟩) (supported 0 ⟨le_rfl, positive.le⟩)
    admissible.1 admissible.2.1 admissible.2.2.2 0
  have initialMomentEquality : (∫ position, omega 0 position * potential (0, position)) =
      ∫ position, initial position * potential (0, position) := integral_congr_ae (initialEquality.mono fun position equality => by
        dsimp only
        rw [equality])
  change Integrable momentumField (spacetimeMeasure horizon) ∧
    Integrable (fun position => ⟪biotSavart initial position, test (0, position)⟫_ℝ) ∧
    (∫ point, momentumField point ∂spacetimeMeasure horizon) + (∫ position, ⟪biotSavart initial position, test (0, position)⟫_ℝ) = 0
  rw [← initialVelocityEquality]
  refine ⟨momentumIntegrable, initialCurl.1, ?_⟩
  have initialIdentity := initialCurl.2
  change (∫ position, ⟪biotSavart (omega 0) position, test (0, position)⟫_ℝ) =
    -(∫ position, omega 0 position * potential (0, position)) at initialIdentity
  rw [initialMomentEquality] at initialIdentity
  linarith [scalarTransport.2.2]

end EulerNonuniqueness
