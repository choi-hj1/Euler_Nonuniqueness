import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Group.Quotient

noncomputable section

open Set

namespace EulerNonuniqueness

theorem continuous_periodic_family_angle {parameter : Type*} [TopologicalSpace parameter]
    (profile : parameter → ℝ → ℝ) (profileContinuous : Continuous (Function.uncurry profile))
    (periodic : ∀ point, Function.Periodic (profile point) (2 * Real.pi)) :
    Continuous (fun point : parameter × Real.Angle => (periodic point.1).lift point.2) := by
  have quotient : IsOpenQuotientMap ((↑) : ℝ → Real.Angle) := QuotientAddGroup.isOpenQuotientMap_mk
  apply (IsOpenQuotientMap.id.prodMap quotient).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, Prod.map, id_eq, Function.Periodic.lift_coe] using profileContinuous

theorem periodic_family_arg_continuousAt {parameter : Type*} [TopologicalSpace parameter]
    (profile : parameter → ℝ → ℝ) (profileContinuous : Continuous (Function.uncurry profile))
    (periodic : ∀ point, Function.Periodic (profile point) (2 * Real.pi))
    {point : parameter × ℂ} (nonzero : point.2 ≠ 0) :
    ContinuousAt (fun next : parameter × ℂ => profile next.1 (Complex.arg next.2)) point := by
  exact (continuous_periodic_family_angle profile profileContinuous periodic).continuousAt.comp
    (continuous_fst.continuousAt.prodMk ((Complex.continuousAt_arg_coe_angle nonzero).comp continuous_snd.continuousAt))

end EulerNonuniqueness
