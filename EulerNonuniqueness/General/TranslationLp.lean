import EulerNonuniqueness.General.ConvolutionContinuity

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem translationMeasurePreserving (offset : ℂ) :
    MeasurePreserving (fun position : ℂ => position - offset) volume volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℂ) (-offset)

def translationLp {Value : Type*} [NormedAddCommGroup Value] {exponent : ℝ≥0∞}
    (field : Lp Value exponent (volume : Measure ℂ)) (offset : ℂ) : Lp Value exponent (volume : Measure ℂ) :=
  Lp.compMeasurePreserving (fun position => position - offset) (translationMeasurePreserving offset) field

theorem continuous_translationLp {Value : Type*} [NormedAddCommGroup Value] {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] (field : Lp Value exponent (volume : Measure ℂ)) (finite : exponent ≠ ∞) :
    Continuous (translationLp field) := by
  let transforms : C(ℂ, C(ℂ, ℂ)) :=
    (⟨fun point : ℂ × ℂ => point.2 - point.1, continuous_snd.sub continuous_fst⟩ : C(ℂ × ℂ, ℂ)).curry
  exact continuous_const.compMeasurePreservingLp transforms.continuous translationMeasurePreserving finite

theorem translationLp_toLp_ae {Value : Type*} [NormedAddCommGroup Value] {exponent : ℝ≥0∞}
    {function : ℂ → Value} (member : MemLp function exponent volume) (offset : ℂ) :
    (translationLp (member.toLp function) offset : ℂ → Value) =ᵐ[volume]
      fun position => function (position - offset) :=
  (Lp.coeFn_compMeasurePreserving (member.toLp function) (translationMeasurePreserving offset)).trans
    ((translationMeasurePreserving offset).quasiMeasurePreserving.ae_eq member.coeFn_toLp)

theorem translationLp_zero {Value : Type*} [NormedAddCommGroup Value] {exponent : ℝ≥0∞}
    (field : Lp Value exponent (volume : Measure ℂ)) : translationLp field 0 = field := by
  apply Lp.ext
  simpa only [translationLp, Function.comp_def, sub_zero] using
    Lp.coeFn_compMeasurePreserving field (translationMeasurePreserving 0)

theorem norm_translationLp_sub_le {Value : Type*} [NormedAddCommGroup Value] {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] (field : Lp Value exponent (volume : Measure ℂ)) (offset : ℂ) :
    ‖translationLp field offset - field‖ ≤ 2 * ‖field‖ := by
  exact (norm_sub_le _ _).trans (by rw [translationLp, Lp.norm_compMeasurePreserving]; nlinarith)

theorem norm_translationLp_toLp_sub {Value : Type*} [NormedAddCommGroup Value] {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] {function : ℂ → Value} (member : MemLp function exponent volume) (offset : ℂ) :
    ‖translationLp (member.toLp function) offset - member.toLp function‖ =
      (eLpNorm (fun position => function (position - offset) - function position) exponent volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (translationLp (member.toLp function) offset) (member.toLp function),
    translationLp_toLp_ae member offset, member.coeFn_toLp] with position subtraction shifted original
  rw [subtraction]
  exact congrArg₂ (fun first second : Value => first - second) shifted original

end EulerNonuniqueness
