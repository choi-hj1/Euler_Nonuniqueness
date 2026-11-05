import EulerNonuniqueness.General.AnalyticGermUniqueness
import EulerNonuniqueness.Section6.NormalFormOrbitCompatibility
import EulerNonuniqueness.Section6.NormalizedOrbitDepartureTarget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compatible_analytic_graph_invariant
    {graph : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) :
    ∀ᶠ unstable : ℝ in 𝓝 0,
      (shapeChartVelocity 1 (unstable, graph unstable)).2 =
        deriv graph unstable * (shapeChartVelocity 1 (unstable, graph unstable)).1 := by
  obtain ⟨comparisonGraph, comparisonCoordinate, comparisonAnalytic, comparisonZero,
    comparisonDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    constant, constantNonnegative, radius, radiusPositive, relative⟩ :=
    exists_uniform_localNormalForm_relative_coordinates
  have graded := fun first second firstSmall secondSmall => by
    simpa only [abs_one, mul_one] using relative 1 first second firstSmall secondSmall
  have stableBound := localNormalForm_stable_bound_of_graded comparisonZero coordinateZero
    constantNonnegative radiusPositive graded
  have comparisonCompatible := normalizedSeparatingOrbit_on_normalForm_graph
    (comparisonAnalytic.contDiffAt (n := 1)) coordinateSmooth.continuousAt comparisonZero
    coordinateZero radiusPositive stableBound orbit normalized
  have unstableLimit : Tendsto (orbitUnstableShape orbit) atBot (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.comp (normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized)
  have punctured : Tendsto (orbitUnstableShape orbit) atBot (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨unstableLimit,
      (normalizedSeparatingOrbit_eventually_positive_unstable orbit normalized).mono
        (fun _ positive => ne_of_gt positive)⟩
  have graphEquality : graph =ᶠ[𝓝 (0 : ℝ)] comparisonGraph :=
    General.analytic_germ_eq_of_eq_along_punctured_curve graphAnalytic comparisonAnalytic punctured
      (by
        filter_upwards [compatible, comparisonCompatible] with time first second
        exact first.symm.trans second)
  have graphSizeContinuous : ContinuousAt (fun unstable : ℝ =>
      |unstable| + |comparisonGraph unstable|) 0 :=
    continuousAt_id.abs.add comparisonAnalytic.continuousAt.abs
  have graphSmall : ∀ᶠ unstable : ℝ in 𝓝 0,
      |unstable| + |comparisonGraph unstable| < radius :=
    graphSizeContinuous.eventually (eventually_lt_nhds (by simpa only [abs_zero,
      comparisonZero, zero_add] using radiusPositive))
  have comparisonInvariant : ∀ᶠ unstable : ℝ in 𝓝 0,
      (shapeChartVelocity 1 (unstable, comparisonGraph unstable)).2 =
        deriv comparisonGraph unstable *
          (shapeChartVelocity 1 (unstable, comparisonGraph unstable)).1 := by
    filter_upwards [graphSmall] with unstable small
    have estimate := graded (unstable, comparisonGraph unstable) 0 small
      (by simpa only [Prod.fst_zero, Prod.snd_zero, abs_zero, zero_add] using radiusPositive)
    have errorZero : localNormalFormError 1 comparisonGraph comparisonCoordinate
        (unstable, comparisonGraph unstable) = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, comparisonZero,
        coordinateZero, sub_self, sub_zero, abs_zero, zero_add, add_zero, zero_mul,
        mul_zero, localNormalFormError_at_zero comparisonZero coordinateZero] using estimate
    have stableZero := congrArg Prod.snd errorZero
    simpa only [localNormalFormError, Prod.snd_zero, sub_self, mul_zero, add_zero,
      sub_eq_zero] using stableZero
  filter_upwards [comparisonInvariant, graphEquality, graphEquality.deriv] with unstable invariant equal derivativeEqual
  rw [equal, derivativeEqual]
  exact invariant

end EulerNonuniqueness.Section6
