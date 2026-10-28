import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationTransportUnit

/-! # Sheafification Unit Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitRestriction

noncomputable section

/-! The canonical sheafification unit preserves an isomorphism detected after geometric restriction. -/

open _root_.CategoryTheory

universe u v u' v' w z

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (A : Type w) [Category.{z} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (P : Dᵒᵖ ⥤ A) (U : Cᵒᵖ)

theorem isIso [IsIso ((toSheafify J (G.op ⋙ P)).app U)] :
    IsIso ((toSheafify K P).app (G.op.obj U)) := by
  let e := SheafificationTransportUnit.comparison G A J K P
  have h := congrArg (fun f => f.app U) (SheafificationTransportUnit.comparison_unit G A J K P)
  change (toSheafify J (G.op ⋙ P)).app U ≫ e.hom.app U =
    (toSheafify K P).app (G.op.obj U) at h
  rw [← h]
  exact IsIso.comp_isIso' inferInstance ((e.app U).isIso_hom)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitRestriction
