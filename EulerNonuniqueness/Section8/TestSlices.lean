import EulerNonuniqueness.Definitions

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem contDiff_spatial_slice {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (time : ℝ) :
    ContDiff ℝ ∞ (fun position => test (time, position)) :=
  smooth.comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_temporal_slice {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (position : Plane) :
    ContDiff ℝ ∞ (fun time => test (time, position)) :=
  smooth.comp (contDiff_id.prodMk contDiff_const)

theorem hasCompactSupport_spatial_slice {test : ℝ × Plane → ℝ}
    (compact : HasCompactSupport test) (time : ℝ) : HasCompactSupport (fun position => test (time, position)) := by
  apply HasCompactSupport.of_support_subset_isCompact (compact.isCompact.image continuous_snd)
  intro position nonzero
  exact ⟨(time, position), subset_tsupport test nonzero, rfl⟩

theorem hasCompactSupport_temporal_slice {test : ℝ × Plane → ℝ}
    (compact : HasCompactSupport test) (position : Plane) : HasCompactSupport (fun time => test (time, position)) := by
  apply HasCompactSupport.of_support_subset_isCompact (compact.isCompact.image continuous_fst)
  intro time nonzero
  exact ⟨(time, position), subset_tsupport test nonzero, rfl⟩

theorem fderiv_spatial_slice {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test)
    (time : ℝ) (position direction : Plane) :
    fderiv ℝ (fun point => test (time, point)) position direction = spatialDerivative test (time, position) direction := by
  have derivative := ((smooth.differentiable (by simp)) (time, position)).hasFDerivAt.comp position
    ((hasFDerivAt_const (time : ℝ) position).prodMk (hasFDerivAt_id position))
  change fderiv ℝ (test ∘ Prod.mk time) position direction = _
  rw [derivative.fderiv]
  rfl

theorem hasDerivAt_temporal_slice {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test)
    (time : ℝ) (position : Plane) :
    HasDerivAt (fun other => test (other, position)) (timeDerivative test (time, position)) time := by
  exact (((smooth.differentiable (by simp)) (time, position)).hasFDerivAt.comp_hasDerivAt time
    ((hasDerivAt_id time).prodMk (hasDerivAt_const time position)))

theorem deriv_temporal_slice {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test)
    (time : ℝ) (position : Plane) :
    deriv (fun other => test (other, position)) time = timeDerivative test (time, position) :=
  (hasDerivAt_temporal_slice smooth time position).deriv

end EulerNonuniqueness
