import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveChowModification
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperModification
import OAI.AlgebraicGeometry.FormalGeometry.Completion.StructureSheafBaseChange

/-! # Chow Modification Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ChowModificationFunctions.Construction

noncomputable section

/-! The actual projective Chow modification preserves normal structure functions after flat base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {A : Scheme.{u}} [IsIntegral A]
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p]

/-- The actual Chow modification has the same functions on every open of a normal target. -/
theorem chowModification_app_isIso
    (hA : ∀ x : A, IsIntegrallyClosed (A.presheaf.stalk x)) (U : A.Opens) :
    IsIso ((Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build p).projection.app U) := by
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build p
  have : IsIntegral D.scheme := D.integral
  have : IsProper D.projection := D.proper
  have : Nonempty D.cover.common := D.cover.common_nonempty
  have : IsIso (D.projection ∣_ D.cover.common) := D.isIso_restrict
  exact Quotients.FiniteDescent.ProperModification.Construction.ProperModificationFunctions.isIso_app hA D.projection D.cover.common U

/-- Flat base change of this actual modification preserves all actual section rings. -/
theorem chowModification_flat_pullback_app_isIso
    (hA : ∀ x : A, IsIntegrallyClosed (A.presheaf.stalk x))
    {Y : Scheme.{u}} (a : Y ⟶ A) [Flat a] (V : Y.Opens) :
    IsIso ((CategoryTheory.Limits.pullback.snd (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build p).projection a).app V) := by
  have : IsProper (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build p).projection :=
    (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build p).proper
  exact StructureSheafBaseChange.Construction.proper_flat_pullback_app_isIso _ a
    (fun U _ => chowModification_app_isIso p hA U) V

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ChowModificationFunctions.Construction
