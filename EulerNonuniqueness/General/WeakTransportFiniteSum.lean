import EulerNonuniqueness.Definitions

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness

theorem weakTransportOn_fintype_sum {index : Type*} [Fintype index]
    {horizon : ℝ} (initial : index → Vorticity) (omega : index → Evolution)
    (velocity : ℝ → Velocity) (transport : ∀ label, WeakTransportOn horizon (initial label) (omega label) velocity) :
    WeakTransportOn horizon (fun position => ∑ label : index, initial label position)
      (fun time position => ∑ label : index, omega label time position) velocity := by
  classical
  intro test properties
  have results := fun label => transport label test properties
  let coefficient := fun point : ℝ × Plane => timeDerivative test point + spatialDerivative test point (velocity point.1 point.2)
  have mainIdentity :
      (fun point : ℝ × Plane => (∑ label : index, omega label point.1 point.2) * coefficient point) =
      fun point => ∑ label : index, omega label point.1 point.2 * coefficient point := by
    funext point
    exact Finset.sum_mul _ _ _
  have initialIdentity : (fun position => (∑ label : index, initial label position) * test (0, position)) =
      fun position => ∑ label : index, initial label position * test (0, position) := by
    funext position
    exact Finset.sum_mul _ _ _
  have mainIntegrable : Integrable (fun point : ℝ × Plane => ∑ label : index,
      omega label point.1 point.2 * coefficient point) (spacetimeMeasure horizon) :=
    integrable_finset_sum _ fun label _ => (results label).1
  have initialIntegrable : Integrable (fun position => ∑ label : index, initial label position * test (0, position)) :=
    integrable_finset_sum _ fun label _ => (results label).2.1
  change Integrable (fun point : ℝ × Plane => (∑ label : index, omega label point.1 point.2) * coefficient point)
      (spacetimeMeasure horizon) ∧ _
  rw [mainIdentity, initialIdentity]
  refine ⟨mainIntegrable, initialIntegrable, ?_⟩
  rw [integral_finset_sum _ (fun label _ => (results label).1),
    integral_finset_sum _ (fun label _ => (results label).2.1), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro label _
  exact (results label).2.2

end EulerNonuniqueness
