import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Analytic.Constructions

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Middle Target : Type*} [PseudoMetricSpace Domain]
  [PseudoMetricSpace Middle] [PseudoMetricSpace Target]

def LipschitzNear (function : Domain → Target) (point : Domain) : Prop :=
  ∃ constant : NNReal, ∃ neighborhood ∈ 𝓝 point, LipschitzOnWith constant function neighborhood

theorem LipschitzNear.continuousAt {function : Domain → Target} {point : Domain}
    (regular : LipschitzNear function point) : ContinuousAt function point := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular
  exact lipschitz.continuousOn.continuousAt nearby

theorem LipschitzNear.comp {outer : Middle → Target} {inner : Domain → Middle} {point : Domain}
    (outerRegular : LipschitzNear outer (inner point)) (innerRegular : LipschitzNear inner point) :
    LipschitzNear (fun current => outer (inner current)) point := by
  obtain ⟨outerConstant, outerSet, outerNearby, outerLip⟩ := outerRegular
  obtain ⟨innerConstant, innerSet, innerNearby, innerLip⟩ := innerRegular
  have innerContinuous : ContinuousAt inner point := innerLip.continuousOn.continuousAt innerNearby
  refine ⟨outerConstant * innerConstant, innerSet ∩ inner ⁻¹' outerSet,
    inter_mem innerNearby (innerContinuous outerNearby), ?_⟩
  exact outerLip.comp (innerLip.mono inter_subset_left)
    ((mapsTo_preimage inner outerSet).mono_left inter_subset_right)

theorem LipschitzNear.prodMk {first : Domain → Middle} {second : Domain → Target} {point : Domain}
    (firstRegular : LipschitzNear first point) (secondRegular : LipschitzNear second point) :
    LipschitzNear (fun current => (first current, second current)) point := by
  obtain ⟨firstConstant, firstSet, firstNearby, firstLip⟩ := firstRegular
  obtain ⟨secondConstant, secondSet, secondNearby, secondLip⟩ := secondRegular
  exact ⟨max firstConstant secondConstant, firstSet ∩ secondSet, inter_mem firstNearby secondNearby,
    (firstLip.mono inter_subset_left).prodMk (secondLip.mono inter_subset_right)⟩

theorem LipschitzNear.congr {first second : Domain → Target} {point : Domain}
    (regular : LipschitzNear first point) (equality : second =ᶠ[𝓝 point] first) :
    LipschitzNear second point := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular
  refine ⟨constant, neighborhood ∩ {current | second current = first current}, inter_mem nearby equality, ?_⟩
  intro initial initialMember final finalMember
  change edist (second initial) (second final) ≤ _
  rw [initialMember.2, finalMember.2]
  exact lipschitz initialMember.1 finalMember.1

variable {Space Range : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem lipschitzNear_of_contDiffAt_one {function : Space → Range} {point : Space}
    (smooth : ContDiffAt ℝ 1 function point) : LipschitzNear function point :=
  smooth.exists_lipschitzOnWith

theorem lipschitzNear_of_analyticAt [CompleteSpace Range] {function : Space → Range} {point : Space}
    (analytic : AnalyticAt ℝ function point) : LipschitzNear function point :=
  lipschitzNear_of_contDiffAt_one analytic.contDiffAt

end

end EulerNonuniqueness.General
