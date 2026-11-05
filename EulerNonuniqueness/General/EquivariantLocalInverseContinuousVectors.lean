import EulerNonuniqueness.General.ContinuousVectorSubmodule
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem PartialHomeomorph.exists_inverse_continuousVector_radius
    (chart : PartialHomeomorph Space Space) (action : ℝ → Space →L[ℝ] Space) (base : Space)
    (sourceZero : (0 : Space) ∈ chart.source) (atZero : chart 0 = base)
    (normPreserved : ∀ offset value, ‖action offset value‖ = ‖value‖)
    (baseFixed : ∀ offset, action offset base = base)
    (equivariant : ∀ offset value, chart (action offset value) = action offset (chart value)) :
    ∃ radius > 0, ∀ data : Space, ‖data - base‖ < radius →
      data ∈ continuousVectorSubmodule action → chart.symm data ∈ continuousVectorSubmodule action := by
  have targetBase : base ∈ chart.target := atZero ▸ chart.map_source sourceZero
  have inverseBase : chart.symm base = 0 := by simpa only [atZero] using chart.left_inv sourceZero
  obtain ⟨sourceRadius, sourcePositive, sourceContained⟩ :=
    Metric.mem_nhds_iff.mp (chart.open_source.mem_nhds sourceZero)
  have inverseNeighborhood : {data : Space | chart.symm data ∈ ball 0 sourceRadius} ∈ 𝓝 base := by
    apply (chart.symm.continuousAt targetBase).preimage_mem_nhds
    rw [inverseBase]
    exact ball_mem_nhds _ sourcePositive
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (chart.open_target.mem_nhds targetBase) inverseNeighborhood)
  refine ⟨radius, positive, ?_⟩
  intro data small member
  have dataBall : data ∈ ball base radius := by simpa only [mem_ball, dist_eq_norm] using small
  have dataTarget := (contained dataBall).1
  have inverseSmall : ‖chart.symm data‖ < sourceRadius := by
    simpa only [mem_setOf_eq, mem_ball, dist_zero_right] using (contained dataBall).2
  have shiftedTarget (offset : ℝ) : action offset data ∈ chart.target := by
    apply (contained ?_).1
    rw [mem_ball, dist_eq_norm, ← baseFixed offset, ← map_sub, normPreserved]
    exact small
  have inverseIdentity (offset : ℝ) : chart.symm (action offset data) = action offset (chart.symm data) := by
    have shiftedSource : action offset (chart.symm data) ∈ chart.source := by
      apply sourceContained
      simpa only [mem_ball, dist_zero_right, normPreserved] using inverseSmall
    have actual := chart.left_inv shiftedSource
    rw [equivariant, chart.right_inv dataTarget] at actual
    exact actual
  have orbit : Continuous (fun offset => action offset data) := member
  have inverseOrbit : Continuous (fun offset => chart.symm (action offset data)) := by
    apply continuous_iff_continuousAt.mpr
    intro offset
    exact ContinuousAt.comp (f := fun parameter : ℝ => action parameter data)
      (g := fun value : Space => chart.symm value) (x := offset)
      (chart.symm.continuousAt (shiftedTarget offset)) (orbit.continuousAt (x := offset))
  change Continuous (fun offset => action offset (chart.symm data))
  simpa only [inverseIdentity] using inverseOrbit

end EulerNonuniqueness.General
