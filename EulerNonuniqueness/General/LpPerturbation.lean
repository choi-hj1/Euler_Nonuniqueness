import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem tendsto_eLpNorm_sub_of_vanishing_perturbation
    {Domain Value Index : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {filter : Filter Index} {exponent : ℝ≥0∞}
    {first second : Index → Domain → Value} {limit : Domain → Value}
    (exponentBound : 1 ≤ exponent)
    (perturbationMeasurable : ∀ index, AEStronglyMeasurable (first index - second index) measure)
    (referenceMeasurable : ∀ index, AEStronglyMeasurable (second index - limit) measure)
    (perturbationConverges : Tendsto (fun index => eLpNorm (first index - second index) exponent measure) filter (𝓝 0))
    (referenceConverges : Tendsto (fun index => eLpNorm (second index - limit) exponent measure) filter (𝓝 0)) :
    Tendsto (fun index => eLpNorm (first index - limit) exponent measure) filter (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using perturbationConverges.add referenceConverges) (fun _ => bot_le)
  intro index
  change eLpNorm (first index - limit) exponent measure ≤
    eLpNorm (first index - second index) exponent measure + eLpNorm (second index - limit) exponent measure
  have identity : first index - limit = (first index - second index) + (second index - limit) := by
    funext point
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  rw [identity]
  exact eLpNorm_add_le (perturbationMeasurable index) (referenceMeasurable index) exponentBound

end MeasureTheory
