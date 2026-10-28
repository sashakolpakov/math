import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Limit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference

/-! # Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Difference

noncomputable section

/-!
# IntegralComparison: compatible bounded sections are the kernel of the sequential difference map
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : D) (F : Cᵒᵖ ⥤ D)

theorem restrict_refl (n : ℕ) (a : ExhaustivePresheafSections.Stage P M F n) : ExhaustivePresheafSections.restrict P hP M F n n le_rfl a = a := by
  apply NatTrans.ext
  funext U
  rfl

theorem restrict_comp (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (a : ExhaustivePresheafSections.Stage P M F l) :
    ExhaustivePresheafSections.restrict P hP M F n m hnm (ExhaustivePresheafSections.restrict P hP M F m l hml a) =
      ExhaustivePresheafSections.restrict P hP M F n l (hnm.trans hml) a := by
  apply NatTrans.ext
  funext U
  rfl

theorem compatible_iff_successor (a : ∀ n, ExhaustivePresheafSections.Stage P M F n) : ExhaustivePresheafSections.Compatible P hP M F a ↔
    ∀ n, ExhaustivePresheafSections.restrict P hP M F n (n + 1) (Nat.le_succ n) (a (n + 1)) = a n := by
  refine ⟨fun h n => h n (n + 1) (Nat.le_succ n), ?_⟩
  intro h n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact restrict_refl P hP M F n (a n)
  | succ m hnm ih =>
    exact (restrict_comp P hP M F n m (m + 1) hnm (Nat.le_succ m) (a (m + 1))).symm.trans
      ((congrArg (ExhaustivePresheafSections.restrict P hP M F n m hnm) (h m)).trans ih)

variable [Preadditive D] (R : Type t) [CommRing R] [Linear R D]

def difference : (∀ n, ExhaustivePresheafSections.Stage P M F n) →ₗ[R] (∀ n, ExhaustivePresheafSections.Stage P M F n) :=
  SequentialModuleDifference.difference R (fun n => ExhaustivePresheafSections.Stage P M F n)
    (fun n => ((Limit.diagram R P hP M F).map (homOfLE (Nat.le_succ n)).op).hom)

theorem compatible_iff_difference_zero (a : ∀ n, ExhaustivePresheafSections.Stage P M F n) :
    ExhaustivePresheafSections.Compatible P hP M F a ↔ difference P hP M F R a = 0 :=
  (compatible_iff_successor P hP M F a).trans
    (SequentialModuleDifference.difference_eq_zero_iff R (fun n => ExhaustivePresheafSections.Stage P M F n)
      (fun n => ((Limit.diagram R P hP M F).map (homOfLE (Nat.le_succ n)).op).hom) a).symm

theorem compatibleSubmodule_eq_ker : ExhaustiveLinearSections.compatibleSubmodule R P hP M F = (difference P hP M F R).ker := by
  apply Submodule.ext
  intro a
  exact compatible_iff_difference_zero P hP M F R a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Difference
