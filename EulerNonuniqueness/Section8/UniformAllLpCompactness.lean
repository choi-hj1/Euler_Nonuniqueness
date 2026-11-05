import EulerNonuniqueness.General.HigherLpConvergence
import EulerNonuniqueness.Section8.UniformVorticityL2Compactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.uniform_vorticity_Lp_convergence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ}
    {limit : Evolution} (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (positive : 0 < horizon)
    (increasing : StrictMono subsequence) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    UniformLpConvergenceOn horizon (ENNReal.ofReal exponent) (sequence ∘ subsequence) limit := by
  obtain ⟨sourceRadius, sourcePositive, sourceSupported⟩ := hypotheses.2.1
  obtain ⟨limitRadius, limitPositive, limitSupported⟩ := path.supported
  let region := Metric.closedBall (0 : Plane) (max sourceRadius limitRadius)
  let measure := volume.restrict region
  letI : IsFiniteMeasure measure := ⟨by
    simpa only [measure, Measure.restrict_apply_univ] using
      (isCompact_closedBall (0 : Plane) (max sourceRadius limitRadius)).measure_lt_top⟩
  let fields := fun index (time : Icc (0 : ℝ) horizon) => sequence (subsequence index) time - limit time
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  have higherBound : 1 ≤ ENNReal.ofReal (exponent + 1) := by
    apply lpBound.trans
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have higherStrict : ENNReal.ofReal exponent < ENNReal.ofReal (exponent + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨sourceBound, sourceFinite, sourceBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound positive.le (show 1 ≤ exponent + 1 by linarith)
  obtain ⟨limitBound, limitFinite, limitBounded⟩ :=
    path.uniformBounds (exponent + 1) (by linarith)
  have sourceMembers (index : ℕ) (time : Icc (0 : ℝ) horizon) :=
    ((hypotheses.2.2 (subsequence index)).2.2.2 (exponent + 1) (by linarith) time time.property).1
  have limitMembers (time : Icc (0 : ℝ) horizon) := path.membership (exponent + 1) (by linarith) time.property
  have measurable (index : ℕ) (time : Icc (0 : ℝ) horizon) : AEStronglyMeasurable (fields index time) measure :=
    ((sourceMembers index time).sub (limitMembers time)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have bounded (index : ℕ) (time : Icc (0 : ℝ) horizon) :
      eLpNorm (fields index time) (ENNReal.ofReal (exponent + 1)) measure ≤
        ENNReal.ofReal (sourceBound.toReal + limitBound.toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal sourceFinite.ne, ENNReal.ofReal_toReal limitFinite.ne]
    apply (eLpNorm_restrict_le _ _ _ _).trans
    exact (eLpNorm_sub_le (sourceMembers index time).aestronglyMeasurable
      (limitMembers time).aestronglyMeasurable higherBound).trans
      (add_le_add (sourceBounded (subsequence index) time time.property) (limitBounded time time.property))
  have differenceSupported (index : ℕ) (time : Icc (0 : ℝ) horizon) :
      Function.support (fields index time) ⊆ region := by
    intro position nonzero
    by_contra outside
    have sourceInside : Function.support (sequence (subsequence index) time) ⊆ region :=
      (sourceSupported (subsequence index) time time.property).trans
        (Metric.closedBall_subset_closedBall (le_max_left _ _))
    have limitInside : Function.support (limit time) ⊆ region :=
      (limitSupported time time.property).trans (Metric.closedBall_subset_closedBall (le_max_right _ _))
    have sourceZero := Function.nmem_support.mp (fun inside => outside (sourceInside inside))
    have limitZero := Function.nmem_support.mp (fun inside => outside (limitInside inside))
    exact nonzero (by simp only [fields, Pi.sub_apply, sourceZero, limitZero, sub_self])
  have twoConvergence := path.uniform_vorticity_L2_convergence hypotheses positive increasing
  have otherConverges (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
      ∀ᶠ index in atTop, ∀ time : Icc (0 : ℝ) horizon,
        eLpNorm (fields index time) 2 measure < ENNReal.ofReal tolerance := by
    obtain ⟨cutoff, afterCutoff⟩ := twoConvergence tolerance tolerancePositive
    refine eventually_atTop.mpr ⟨cutoff, fun index lower time => ?_⟩
    exact (eLpNorm_restrict_le _ _ _ _).trans_lt (afterCutoff index lower time time.property)
  intro tolerance tolerancePositive
  have upgraded := eventually_uniform_eLpNorm_lt_of_uniform_other_eLpNorm_lt
    lpBound higherStrict (by simp) (by norm_num : (2 : ℝ≥0∞) ≠ 0) measurable
    (show 0 ≤ sourceBound.toReal + limitBound.toReal by positivity) bounded otherConverges tolerancePositive
  obtain ⟨cutoff, afterCutoff⟩ := eventually_atTop.mp upgraded
  refine ⟨cutoff, fun index lower time inside => ?_⟩
  have estimate := afterCutoff index lower ⟨time, inside⟩
  simpa only [measure, eLpNorm_restrict_eq_of_support_subset (differenceSupported _ _)] using estimate

end EulerNonuniqueness
