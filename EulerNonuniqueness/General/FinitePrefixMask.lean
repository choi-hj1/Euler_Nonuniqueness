import Mathlib.Analysis.Normed.Group.Constructions

namespace EulerNonuniqueness.General

theorem norm_prefix_with_receiver_le
    {Index Value : Type*} [Fintype Index] [LinearOrder Index] [SeminormedAddCommGroup Value]
    (states : Index → Value) (receiver drive : Index) (below : receiver ≤ drive) :
    ‖fun source : Index => if source < drive ∨ source = receiver then states source else 0‖ ≤
      ‖fun source : Index => if source < drive then states source else 0‖ +
        (if receiver = drive then ‖states drive‖ else 0) := by
  classical
  have extraNonnegative : 0 ≤ if receiver = drive then ‖states drive‖ else 0 := by
    split
    · exact norm_nonneg _
    · exact le_rfl
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) extraNonnegative)).mpr
  intro source
  by_cases selected : source < drive ∨ source = receiver
  · simp only [selected, ite_true]
    by_cases follower : source < drive
    · have component := norm_le_pi_norm (fun source : Index => if source < drive then states source else 0) source
      simp only [follower, ite_true] at component
      exact component.trans (le_add_of_nonneg_right extraNonnegative)
    · have sameReceiver : source = receiver := selected.resolve_left follower
      have receiverNotLt : ¬receiver < drive := by simpa only [sameReceiver] using follower
      have sameDrive : receiver = drive := le_antisymm below (not_lt.mp receiverNotLt)
      simp only [sameReceiver, sameDrive, ite_true]
      exact le_add_of_nonneg_left (norm_nonneg _)
  · simp only [selected, ite_false, norm_zero]
    exact add_nonneg (norm_nonneg _) extraNonnegative

theorem norm_prefix_with_receiver_nonnegative_le
    {Index : Type*} [Fintype Index] [LinearOrder Index]
    (states : Index → ℝ) (nonnegative : ∀ source, 0 ≤ states source)
    (receiver drive : Index) (below : receiver ≤ drive) :
    ‖fun source : Index => if source < drive ∨ source = receiver then states source else 0‖ ≤
      ‖fun source : Index => if source < drive then states source else 0‖ +
        (if receiver = drive then states drive else 0) := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (nonnegative drive)] using
    norm_prefix_with_receiver_le states receiver drive below

end EulerNonuniqueness.General
