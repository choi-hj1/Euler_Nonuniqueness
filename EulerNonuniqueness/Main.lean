import EulerNonuniqueness.Section4.ReferenceStatement
import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.Section8.Assembly

/-!
# Conditional construction interface

This module records an implication from two finite-patch specifications and an extraction hypothesis.
The unconditional proof is `EulerNonuniqueness.theorem11` in `Theorem11.lean`, using actual approximation data.
The inputs of this conditional interface are explicit hypotheses, not axioms or prerequisites of that closed proof.
-/

namespace EulerNonuniqueness

/-- Extraction interface from the two finite-patch specifications to actual global approximation sequences with a common initial limit and a fixed positive observation gap. The unconditional approximation construction is proved separately by `Paper.exists_actual_approximation_data`; this definition does not assert either packaged finite-patch specification. -/
def FiniteConstructionExtraction : Prop :=
  Paper.Proposition41Statement → Paper.Proposition51ExistenceStatement →
    Nonempty ApproximationData

theorem main_conditional
    (referencePreparation : Paper.Proposition41Statement)
    (finiteCascade : Paper.Proposition51ExistenceStatement)
    (finiteConstruction : FiniteConstructionExtraction) : Theorem11 := by
  obtain ⟨data⟩ := finiteConstruction referencePreparation finiteCascade
  exact nonuniqueness_of_approximation_data data

end EulerNonuniqueness
