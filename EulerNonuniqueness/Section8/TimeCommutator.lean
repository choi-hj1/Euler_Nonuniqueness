import EulerNonuniqueness.Section8.MollifiedTransport
import EulerNonuniqueness.Section8.TimeFluxContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.continuous_biotSavart_time
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ) (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon => biotSavart (sequence index time) position) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  obtain ⟨normBound, normBoundFinite, normBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 4)
  apply continuous_iff_continuousAt.mpr
  intro time
  apply tendsto_biotSavart_of_weakL2_uniform_memLp_support
    holderConjugate_four_fourThirds (by norm_num) radiusPositive.le
    (fun other : Icc (0 : ℝ) horizon =>
      ((hypotheses.2.2 index).2.2.2 4 (by norm_num) other other.property).1)
    (((hypotheses.2.2 index).2.2.2 4 (by norm_num) time time.property).1)
    (fun other : Icc (0 : ℝ) horizon => supported index other other.property)
    (supported index time time.property) (bound := normBound.toReal)
  · intro other
    exact ENNReal.toReal_mono normBoundFinite.ne (normBounded index other other.property)
  · intro test testMember
    exact ((hypotheses.2.2 index).2.1.2 test testMember).tendsto time

theorem fderiv_scalarConvolution_apply_source {source kernel : Plane → ℝ}
    (integrable : Integrable source) (smooth : ContDiff ℝ ∞ kernel)
    (compact : HasCompactSupport kernel) (position direction : Plane) :
    fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) position direction =
      ∫ point, source point * fderiv ℝ kernel (position - point) direction := by
  rw [fderiv_scalarConvolution_apply integrable smooth compact]
  have equality := integral_sub_left_eq_self
    (fun offset => source (position - offset) * fderiv ℝ kernel offset direction) volume position
  simpa only [sub_sub_cancel] using equality.symm

theorem LocalCompactnessHypotheses.continuous_mollifiedDerivative_time
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (index : ℕ)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    (position direction : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon =>
      fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] sequence index time) position direction) := by
  have testSmooth : ContDiff ℝ ∞ (fun point => fderiv ℝ kernel (position - point) direction) :=
    (contDiff_directionalDerivative smooth direction).comp (contDiff_const.sub contDiff_id)
  have testCompact : HasCompactSupport (fun point => fderiv ℝ kernel (position - point) direction) :=
    (compact.fderiv_apply ℝ direction).comp_homeomorph (Homeomorph.subLeft position)
  have result := (hypotheses.2.2 index).2.1.2 _
    (testSmooth.continuous.memLp_of_hasCompactSupport testCompact)
  convert result using 1
  funext time
  exact fderiv_scalarConvolution_apply_source
    (memLp_one_iff_integrable.mp (by simpa using
      ((hypotheses.2.2 index).2.2.2 1 le_rfl time time.property).1)) smooth compact position direction

theorem LocalCompactnessHypotheses.continuous_transportCommutator_time
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon =>
      transportCommutator kernel (biotSavart (sequence index time)) (sequence index time) position) := by
  have reflectedSmooth : ContDiff ℝ ∞ (fun point => kernel (position - point)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have reflectedCompact : HasCompactSupport (fun point => kernel (position - point)) :=
    compact.comp_homeomorph (Homeomorph.subLeft position)
  have fluxContinuous := hypotheses.continuous_transportFlux horizonNonnegative index reflectedSmooth reflectedCompact
  have velocityContinuous := hypotheses.continuous_biotSavart_time horizonNonnegative index position
  have firstContinuous :=
    (((Complex.continuous_re.comp velocityContinuous).mul
      (hypotheses.continuous_mollifiedDerivative_time index smooth compact position 1)).add
      ((Complex.continuous_im.comp velocityContinuous).mul
        (hypotheses.continuous_mollifiedDerivative_time index smooth compact position Complex.I)))
  convert firstContinuous.add fluxContinuous using 1
  funext time
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  have members := fun exponent bound => ((hypotheses.2.2 index).2.2.2 exponent bound time time.property).1
  have integrable : Integrable (sequence index time) :=
    memLp_one_iff_integrable.mp (by simpa using members 1 le_rfl)
  rw [transportCommutator_eq_mollifiedTransport integrable
    (integrable_vorticity_smul_biotSavart radiusPositive.le members
      (supported index time time.property) ((hypotheses.2.2 index).2.2.1 time time.property).2) smooth compact]
  rw [realLinearMap_apply_complex]
  have changeVariables := integral_sub_left_eq_self
    (fun offset => sequence index time (position - offset) *
      fderiv ℝ kernel offset (biotSavart (sequence index time) (position - offset))) volume position
  simp only [sub_sub_cancel] at changeVariables
  rw [← changeVariables]
  simp_rw [fderiv_reflected_test smooth, ContinuousLinearMap.neg_apply, mul_neg]
  rw [integral_neg]
  simp only [Function.comp_apply]
  ring

theorem LocalCompactnessHypotheses.measurable_transportCommutator
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel) :
    Measurable (fun point : Icc (0 : ℝ) horizon × Plane =>
      transportCommutator kernel (biotSavart (sequence index point.1)) (sequence index point.1) point.2) := by
  have spatialContinuous (time : Icc (0 : ℝ) horizon) : Continuous
      (transportCommutator kernel (biotSavart (sequence index time)) (sequence index time)) := by
    obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
    have members := fun exponent bound => ((hypotheses.2.2 index).2.2.2 exponent bound time time.property).1
    exact continuous_transportCommutator
      (memLp_one_iff_integrable.mp (by simpa using members 1 le_rfl))
      (integrable_vorticity_smul_biotSavart radiusPositive.le members
        (supported index time time.property) ((hypotheses.2.2 index).2.2.1 time time.property).2)
      (hypotheses.continuous_biotSavart index time.property) smooth compact
  have reversed := measurable_uncurry_of_continuous_of_measurable spatialContinuous
    (fun position => (hypotheses.continuous_transportCommutator_time
      horizonNonnegative index smooth compact position).measurable)
  exact reversed.comp measurable_swap

end EulerNonuniqueness
