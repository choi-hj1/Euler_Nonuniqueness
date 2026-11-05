import EulerNonuniqueness.Section8.RenormalizedEndpointFTC

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.integrable_renormalized_commutator
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization) (index : ℕ) :
    Integrable (fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
      transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2)
      (spacetimeMeasure horizon) := by
  obtain ⟨bound, nonnegativeBound, bounded⟩ := admissible.2
  have measurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2) nonnegative
    (hypotheses.measurable_mollification index)
  exact (hypotheses.integrable_transportCommutator_spacetime nonnegative index).bdd_mul
    ((admissible.1.continuous_deriv le_rfl).comp_aestronglyMeasurable measurable)
    ⟨bound, fun point => by simpa only [Real.norm_eq_abs] using bounded _⟩

theorem TransportAnalyticHypotheses.renormalized_mollification_mass_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    (zero : renormalization 0 = 0) (index : ℕ) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ position, renormalization (mollification (omega time) index position)) -
      (∫ position, renormalization (mollification (omega 0) index position)) =
      ∫ point : ℝ × Plane, deriv renormalization (mollification (omega point.1) index point.2) *
        transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2
          ∂spacetimeMeasure time := by
  let error := fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
    transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2
  let advection := fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
    fderiv ℝ (mollification (omega point.1) index) point.2 (biotSavart (omega point.1) point.2)
  have errorIntegrable : Integrable error (spacetimeMeasure time) :=
    (hypotheses.integrable_renormalized_commutator positive.le admissible index).mono_measure (spacetimeMeasure_mono inside.2)
  have advectionIntegrable : Integrable advection (spacetimeMeasure time) :=
    (hypotheses.integrable_renormalized_mollified_advection positive.le admissible index).mono_measure (spacetimeMeasure_mono inside.2)
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  have endpointIntegrable (endpoint : ℝ) (endpointInside : endpoint ∈ Icc 0 horizon) :
      Integrable (fun position => renormalization (mollification (omega endpoint) index position)) :=
    (admissible.1.continuous.comp (contDiff_mollification (hypotheses.integrable endpointInside) index).continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_mollification (supported endpoint endpointInside) index).comp_left zero)
  have endpointIdentity (position : Plane) :
      (∫ other in Ioo 0 time, error (other, position) - advection (other, position)) =
        renormalization (mollification (omega time) index position) - renormalization (mollification (omega 0) index position) := by
    convert hypotheses.renormalized_mollification_endpoint_identity positive admissible.1 index position inside using 1
    congr 1
    funext other
    dsimp [error, advection]
    ring
  have identity := integral_prod_symm _ (errorIntegrable.sub advectionIntegrable)
  change (∫ point, error point - advection point ∂spacetimeMeasure time) =
    (∫ position, ∫ other in Ioo 0 time, error (other, position) - advection (other, position)) at identity
  simp_rw [endpointIdentity] at identity
  rw [integral_sub errorIntegrable advectionIntegrable,
    integral_sub (endpointIntegrable time inside) (endpointIntegrable 0 ⟨le_rfl, positive.le⟩)] at identity
  have advectionZero : (∫ point, advection point ∂spacetimeMeasure time) = 0 := by
    change (∫ point, advection point ∂((volume.restrict (Ioo 0 time)).prod volume)) = 0
    rw [integral_prod advection advectionIntegrable]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with other otherInside
    have closedInside : other ∈ Icc 0 horizon := ⟨otherInside.1.le, otherInside.2.le.trans inside.2⟩
    exact (integral_renormalized_mollified_advection_eq_zero radiusPositive
      (fun exponent bound => hypotheses.membership exponent bound other closedInside)
      (supported other closedInside) admissible.1 zero index).2
  rw [advectionZero, sub_zero] at identity
  exact identity.symm

end EulerNonuniqueness
