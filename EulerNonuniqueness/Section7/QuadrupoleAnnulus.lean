import EulerNonuniqueness.Section3.BoundaryDomainConfinement
import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.General.MidpointAnnulus

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

def firstDipoleCenter {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count) : ℂ :=
  (patchCentroid motion time index 0 + patchCentroid motion time index 3) / 2

def secondDipoleCenter {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count) : ℂ :=
  (patchCentroid motion time index 1 + patchCentroid motion time index 2) / 2

theorem quadrupoleCenter_eq_dipole_midpoint {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    quadrupoleCenter motion time index = midpoint ℝ (firstDipoleCenter motion time index)
      (secondDipoleCenter motion time index) := by
  simp [quadrupoleCenter, firstDipoleCenter, secondDipoleCenter, Fin.sum_univ_succ,
    midpoint_eq_smul_add, invOf_eq_inv, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

theorem pairCenterDistance_eq_dist {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    pairCenterDistance motion time index = dist (firstDipoleCenter motion time index)
      (secondDipoleCenter motion time index) := by
  rfl

theorem patchCentroid_near_dipole_center {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) {diameter : ℝ}
    (firstLength : ‖patchCentroid motion time index 0 - patchCentroid motion time index 3‖ ≤ diameter)
    (secondLength : ‖patchCentroid motion time index 1 - patchCentroid motion time index 2‖ ≤ diameter)
    (patch : Fin 4) :
    dist (patchCentroid motion time index patch)
      (if patch = 0 ∨ patch = 3 then firstDipoleCenter motion time index else secondDipoleCenter motion time index) ≤
        diameter / 2 := by
  have normIdentity (first second : ℂ) : ‖first - (first + second) / 2‖ = ‖first - second‖ / 2 := by
    rw [show first - (first + second) / 2 = (first - second) / 2 by ring, norm_div]
    norm_num
  have reverseIdentity (first second : ℂ) : ‖second - (first + second) / 2‖ = ‖first - second‖ / 2 := by
    rw [show second - (first + second) / 2 = -(first - second) / 2 by ring, norm_div, norm_neg]
    norm_num
  fin_cases patch <;> simp [firstDipoleCenter, secondDipoleCenter, dist_eq_norm]
  · rw [normIdentity]
    linarith
  · rw [normIdentity]
    linarith
  · rw [reverseIdentity]
    linarith
  · rw [reverseIdentity]
    linarith

theorem quadrupole_domain_annular_estimate {count : ℕ} {motion : PatchMotion count}
    {time : ℝ} {index : Fin count} {center : ℂ} {diameter domainRadius centerError : ℝ}
    (firstLength : ‖patchCentroid motion time index 0 - patchCentroid motion time index 3‖ ≤ diameter)
    (secondLength : ‖patchCentroid motion time index 1 - patchCentroid motion time index 2‖ ≤ diameter)
    (centerControl : ‖quadrupoleCenter motion time index - center‖ ≤ centerError)
    (domains : ∀ patch, motion.domain time index patch ⊆
      Metric.closedBall (patchCentroid motion time index patch) domainRadius)
    (patch : Fin 4) (position : ℂ) (inside : position ∈ motion.domain time index patch) :
    pairCenterDistance motion time index / 2 - domainRadius - diameter / 2 - centerError ≤ ‖position - center‖ ∧
      ‖position - center‖ ≤ pairCenterDistance motion time index / 2 + domainRadius + diameter / 2 + centerError := by
  let pairCenter := if patch = 0 ∨ patch = 3 then firstDipoleCenter motion time index
    else secondDipoleCenter motion time index
  have pointNear : dist position pairCenter ≤ domainRadius + diameter / 2 :=
    (dist_triangle position (patchCentroid motion time index patch) pairCenter).trans
      (add_le_add (domains patch inside) (patchCentroid_near_dipole_center motion time index firstLength secondLength patch))
  have nearMiddle : dist center (midpoint ℝ (firstDipoleCenter motion time index)
      (secondDipoleCenter motion time index)) ≤ centerError := by
    rw [← quadrupoleCenter_eq_dipole_midpoint, dist_comm, dist_eq_norm]
    exact centerControl
  by_cases firstPair : patch = 0 ∨ patch = 3
  · have estimate := dist_annulus_of_dist_midpoint_le (by simpa only [pairCenter, if_pos firstPair] using pointNear) nearMiddle
    rw [← pairCenterDistance_eq_dist, dist_eq_norm] at estimate
    constructor <;> linarith [estimate.1, estimate.2]
  · have estimate := dist_annulus_of_dist_midpoint_le
      (by simpa only [pairCenter, if_neg firstPair] using pointNear)
      (by simpa only [midpoint_comm] using nearMiddle)
    rw [dist_comm (secondDipoleCenter motion time index), ← pairCenterDistance_eq_dist, dist_eq_norm] at estimate
    constructor <;> linarith [estimate.1, estimate.2]

theorem FinitePatchEvolution.domain_annular_estimate {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time boundaryError diameter centerError : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {center : ℂ}
    (boundaryControl : ∀ patch, BoundaryCloseToCircle scales motion time index patch boundaryError)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (firstLength : ‖patchCentroid motion time index 0 - patchCentroid motion time index 3‖ ≤ diameter)
    (secondLength : ‖patchCentroid motion time index 1 - patchCentroid motion time index 2‖ ≤ diameter)
    (centerControl : ‖quadrupoleCenter motion time index - center‖ ≤ centerError)
    (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time index patch) :
    pairCenterDistance motion time index / 2 - scales.radius (index.val + 1) * (1 + boundaryError) -
        diameter / 2 - centerError ≤ ‖position - center‖ ∧
      ‖position - center‖ ≤ pairCenterDistance motion time index / 2 +
        scales.radius (index.val + 1) * (1 + boundaryError) + diameter / 2 + centerError :=
  quadrupole_domain_annular_estimate firstLength secondLength centerControl
    (fun patch => evolution.domain_subset_centroid_ball inside index patch (boundaryControl patch) radiusPositive)
    patch position member

end EulerNonuniqueness.Paper
