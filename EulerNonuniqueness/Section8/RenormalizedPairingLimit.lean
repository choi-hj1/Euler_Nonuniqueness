import EulerNonuniqueness.Section8.RenormalizationL2
import EulerNonuniqueness.Section8.MollificationTimeConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.renormalized_mollification_pairing_limit
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {coefficient : ℝ × Plane → ℝ} {coefficientBound : ℝ}
    (coefficientMeasurable : AEStronglyMeasurable coefficient (spacetimeMeasure horizon))
    (coefficientIntegrable : Integrable coefficient (spacetimeMeasure horizon))
    (coefficientMembers : ∀ time ∈ Ioo 0 horizon, MemLp (fun position => coefficient (time, position)) 2 volume)
    (coefficientBounded : ∀ time ∈ Ioo 0 horizon,
      (eLpNorm (fun position => coefficient (time, position)) 2 volume).toReal ≤ coefficientBound)
    (coefficientNonnegative : 0 ≤ coefficientBound) :
    Integrable (fun point => renormalization (omega point.1 point.2) * coefficient point) (spacetimeMeasure horizon) ∧
      (∀ index, Integrable (fun point => renormalization (mollification (omega point.1) index point.2) * coefficient point)
        (spacetimeMeasure horizon)) ∧
      Tendsto (fun index => ∫ point : ℝ × Plane,
        renormalization (mollification (omega point.1) index point.2) * coefficient point ∂spacetimeMeasure horizon)
        atTop (𝓝 (∫ point : ℝ × Plane, renormalization (omega point.1 point.2) * coefficient point ∂spacetimeMeasure horizon)) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  obtain ⟨sourceBound, sourceFinite, sourceBounded⟩ := hypotheses.uniformBounds 2 (by norm_num)
  obtain ⟨lipschitzBound, lipschitzNonnegative, lipschitzBounded⟩ := admissible.exists_norm_sub_bound
  have timeInside : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon), time ∈ Ioo 0 horizon := ae_restrict_mem measurableSet_Ioo
  have sourceMembers : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon), MemLp (omega time) 2 volume := by
    filter_upwards [timeInside] with time inside
    exact hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩
  have sourceRealBound (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (eLpNorm (omega time) 2 volume).toReal ≤ sourceBound.toReal :=
    ENNReal.toReal_mono sourceFinite.ne (by simpa using sourceBounded time ⟨inside.1.le, inside.2.le⟩)
  have sourceBoundAE : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon),
      (eLpNorm (omega time) 2 volume).toReal ≤ sourceBound.toReal := timeInside.mono fun time inside => sourceRealBound time inside
  have coefficientMembersAE := timeInside.mono fun time inside => coefficientMembers time inside
  have coefficientBoundAE := timeInside.mono fun time inside => coefficientBounded time inside
  have sourceMeasurable := hypotheses.weakTransport.aestronglyMeasurable
  have mollifiedMeasurable (index : ℕ) := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2) nonnegative
    (hypotheses.measurable_mollification index)
  have mollifiedMember (index : ℕ) (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      MemLp (mollification (omega time) index) 2 volume :=
    (contDiff_mollification (hypotheses.integrable ⟨inside.1.le, inside.2.le⟩) index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification (supported time ⟨inside.1.le, inside.2.le⟩) index)
  have mollifiedRealBound (index : ℕ) (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (eLpNorm (mollification (omega time) index) 2 volume).toReal ≤ sourceBound.toReal := by
    have contraction : eLpNorm (mollification (omega time) index) 2 volume ≤ eLpNorm (omega time) 2 volume := by
      simpa using eLpNorm_mollification_nat_le (hypotheses.integrable ⟨inside.1.le, inside.2.le⟩)
        (supported time ⟨inside.1.le, inside.2.le⟩) (power := 2) (by norm_num)
        (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩) index
    exact (ENNReal.toReal_mono (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩).eLpNorm_lt_top.ne contraction).trans
      (sourceRealBound time inside)
  have targetIntegrable := integrable_renormalization_prod_mul_of_uniform_L2 admissible
    (fieldBound := sourceBound.toReal) ENNReal.toReal_nonneg sourceMeasurable coefficientMeasurable coefficientIntegrable
    sourceMembers coefficientMembersAE sourceBoundAE coefficientBoundAE
  have sequenceIntegrable (index : ℕ) := integrable_renormalization_prod_mul_of_uniform_L2 admissible
    (fieldBound := sourceBound.toReal) ENNReal.toReal_nonneg (mollifiedMeasurable index) coefficientMeasurable coefficientIntegrable
    (timeInside.mono fun time inside => mollifiedMember index time inside) coefficientMembersAE
    (timeInside.mono fun time inside => mollifiedRealBound index time inside) coefficientBoundAE
  refine ⟨targetIntegrable, sequenceIntegrable, ?_⟩
  let difference := fun index (point : ℝ × Plane) =>
    renormalization (mollification (omega point.1) index point.2) - renormalization (omega point.1 point.2)
  have differenceResults (index : ℕ) (time : ℝ) (inside : time ∈ Ioo 0 horizon) :=
    memLp_renormalization_sub_two (mollifiedMember index time inside)
      (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩)
      admissible.1.continuous lipschitzNonnegative lipschitzBounded
  have differenceMeasurable (index : ℕ) : AEStronglyMeasurable (difference index) (spacetimeMeasure horizon) :=
    (admissible.1.continuous.comp_aestronglyMeasurable (mollifiedMeasurable index)).sub
      (admissible.1.continuous.comp_aestronglyMeasurable sourceMeasurable)
  have differenceBound (index : ℕ) (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (eLpNorm (fun position => difference index (time, position)) 2 volume).toReal ≤
        lipschitzBound * (2 * sourceBound.toReal) := by
    apply (differenceResults index time inside).2.trans
    exact mul_le_mul_of_nonneg_left ((toReal_eLpNorm_mollification_sub_two_le
      (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩)
      (supported time ⟨inside.1.le, inside.2.le⟩) (hypotheses.integrable ⟨inside.1.le, inside.2.le⟩) index).trans
        (mul_le_mul_of_nonneg_left (sourceRealBound time inside) (by norm_num))) lipschitzNonnegative
  have errorIntegrable (index : ℕ) : Integrable (fun point => difference index point * coefficient point)
      (spacetimeMeasure horizon) := integrable_prod_mul_of_uniform_L2
    (first := difference index) (second := coefficient)
    (firstBound := lipschitzBound * (2 * sourceBound.toReal)) (secondBound := coefficientBound)
    (differenceMeasurable index) coefficientMeasurable
    (timeInside.mono fun time inside => (differenceResults index time inside).1) coefficientMembersAE
    (timeInside.mono fun time inside => differenceBound index time inside) coefficientBoundAE (by positivity)
  have sourceDifferenceBound (index : ℕ) : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon),
      (eLpNorm (mollification (omega time) index - omega time) 2 volume).toReal ≤ 2 * sourceBound.toReal := by
    filter_upwards [timeInside] with time inside
    exact (toReal_eLpNorm_mollification_sub_two_le
      (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩)
      (supported time ⟨inside.1.le, inside.2.le⟩) (hypotheses.integrable ⟨inside.1.le, inside.2.le⟩) index).trans
        (mul_le_mul_of_nonneg_left (sourceRealBound time inside) (by norm_num))
  have sourceDifferenceIntegrable (index : ℕ) : Integrable
      (fun time => (eLpNorm (mollification (omega time) index - omega time) 2 volume).toReal)
      (volume.restrict (Ioo 0 horizon)) := by
    exact integrable_toReal_eLpNorm_two_prod_of_bound
      (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2 - omega point.1 point.2)
      ((mollifiedMeasurable index).sub sourceMeasurable)
      (timeInside.mono fun time inside => (mollifiedMember index time inside).sub
        (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩)) (sourceDifferenceBound index)
  have errorConverges : Tendsto (fun index => ∫ point : ℝ × Plane,
      difference index point * coefficient point ∂spacetimeMeasure horizon) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have boundConverges := (tendsto_const_nhds (x := lipschitzBound * coefficientBound)).mul
      (hypotheses.tendsto_integral_mollification_sub_two_norm nonnegative)
    apply squeeze_zero (fun _ => norm_nonneg _) (fun index => ?_) (by simpa only [mul_zero] using boundConverges)
    calc
      _ ≤ ∫ point : ℝ × Plane, ‖difference index point * coefficient point‖ ∂spacetimeMeasure horizon :=
        norm_integral_le_integral_norm _
      _ = ∫ time in Ioo 0 horizon, ∫ position, ‖difference index (time, position) * coefficient (time, position)‖ :=
        integral_prod _ (errorIntegrable index).norm
      _ ≤ ∫ time in Ioo 0 horizon, (lipschitzBound * coefficientBound) *
          (eLpNorm (mollification (omega time) index - omega time) 2 volume).toReal := by
        apply integral_mono_ae (errorIntegrable index).norm.integral_prod_left
          ((sourceDifferenceIntegrable index).const_mul _)
        filter_upwards [timeInside] with time inside
        have holder := integral_norm_mul_norm_le_eLpNorm_two (differenceResults index time inside).1 (coefficientMembers time inside)
        calc
          _ ≤ (eLpNorm (fun position => difference index (time, position)) 2 volume).toReal *
              (eLpNorm (fun position => coefficient (time, position)) 2 volume).toReal := by simpa only [norm_mul] using holder
          _ ≤ (lipschitzBound * (eLpNorm (mollification (omega time) index - omega time) 2 volume).toReal) * coefficientBound :=
            mul_le_mul (differenceResults index time inside).2 (coefficientBounded time inside) ENNReal.toReal_nonneg (by positivity)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  have identity (index : ℕ) : (∫ point : ℝ × Plane, difference index point * coefficient point ∂spacetimeMeasure horizon) =
      (∫ point : ℝ × Plane, renormalization (mollification (omega point.1) index point.2) * coefficient point ∂spacetimeMeasure horizon) -
        ∫ point : ℝ × Plane, renormalization (omega point.1 point.2) * coefficient point ∂spacetimeMeasure horizon := by
    simp only [difference, sub_mul]
    exact integral_sub (sequenceIntegrable index) targetIntegrable
  simp_rw [identity] at errorConverges
  have result := errorConverges.add (tendsto_const_nhds (x := ∫ point : ℝ × Plane,
    renormalization (omega point.1 point.2) * coefficient point ∂spacetimeMeasure horizon))
  simpa only [sub_add_cancel, zero_add] using result

end EulerNonuniqueness
