import EulerNonuniqueness.Definitions
import Mathlib.Analysis.Convolution

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

def horizontalTestSlice (test : ℝ × Plane → Plane) (point : ℝ × Plane) (horizontal : ℝ) : ℝ :=
  (test (point.1, (horizontal : ℂ) + (point.2.im : ℂ) * Complex.I)).im

def horizontalHeaviside : ℝ → ℝ := (Ici 0).indicator (fun _ => 1)

def streamFunction (test : ℝ × Plane → Plane) (point : ℝ × Plane) : ℝ :=
  (horizontalHeaviside ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] horizontalTestSlice test point) point.2.re

theorem horizontalTestSlice_contDiff {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) :
    ContDiff ℝ ∞ (Function.uncurry (horizontalTestSlice test)) := by
  have horizontal : ContDiff ℝ ∞ (fun point : (ℝ × Plane) × ℝ => (point.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have vertical : ContDiff ℝ ∞ (fun point : (ℝ × Plane) × ℝ => ((point.1.2.im : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp (contDiff_snd.comp contDiff_fst))
  exact Complex.imCLM.contDiff.comp (smooth.comp
    ((contDiff_fst.comp contDiff_fst).prodMk (horizontal.add (vertical.mul contDiff_const))))

theorem horizontalTestSlice_uniform_support {test : ℝ × Plane → Plane} (compact : HasCompactSupport test) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ point horizontal,
      horizontal ∉ Metric.closedBall (0 : ℝ) radius → horizontalTestSlice test point horizontal = 0 := by
  obtain ⟨radius, positive, bounded⟩ :=
    (compact.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  refine ⟨radius, positive, fun point horizontal outside => ?_⟩
  have testZero : test (point.1, (horizontal : ℂ) + (point.2.im : ℂ) * Complex.I) = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    intro inside
    apply outside
    have estimate := bounded _ ⟨_, inside, rfl⟩
    have coordinate := Complex.abs_re_le_norm ((horizontal : ℂ) + (point.2.im : ℂ) * Complex.I)
    have bound : |horizontal| ≤ radius := by simpa using coordinate.trans estimate
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using bound
  simp only [horizontalTestSlice, testZero, Complex.zero_im]

theorem contDiff_streamFunction {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) : ContDiff ℝ ∞ (streamFunction test) := by
  obtain ⟨radius, positive, supported⟩ := horizontalTestSlice_uniform_support compact
  have heavisideIntegrable : LocallyIntegrable horizontalHeaviside (volume : Measure ℝ) :=
    (continuous_const.locallyIntegrable (f := fun _ : ℝ => (1 : ℝ))).indicator measurableSet_Ici
  have result := contDiffOn_convolution_right_with_param_comp (ContinuousLinearMap.mul ℝ ℝ)
    (Complex.reCLM.contDiff.comp contDiff_snd).contDiffOn isOpen_univ (isCompact_closedBall (0 : ℝ) radius)
    (fun point horizontal _ outside => supported point horizontal outside) heavisideIntegrable
    (horizontalTestSlice_contDiff smooth).contDiffOn
  exact contDiffOn_univ.mp result

end EulerNonuniqueness
