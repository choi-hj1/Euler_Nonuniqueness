import EulerNonuniqueness.Section1.OuterCirculationTail
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_outer_field_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) (outer : index.val = 0)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    ‖biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index)‖ ≤
      (96 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 2) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  exact (evolution.externalPatch_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive index
    (referenceSourceDistance scales index) geometry.positive geometry.centerSeparated geometry.centerSeparated).1.trans
      (scales.outer_foreign_velocity_weight_le frequencyBound ratioBound alphaPositive index outer)

end EulerNonuniqueness.Paper
