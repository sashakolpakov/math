import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MeetRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation

/-! # Local Cone -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone

noncomputable section

/-! Invertible meet restrictions give a canonical cone from the chart
coefficient, and every original natural cone factors through this cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable (C : Type u) [SemilatticeInf C] (I : C)
  {A : Type v} [Category.{w} A] (P : Cᵒᵖ ⥤ A)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def meetCone : (Functor.const Cᵒᵖ).obj (P.obj (op I)) ⟶
    (MeetRestriction.SemilatticeMeetRestriction.restriction C I).op ⋙ (MeetRestriction.SemilatticeMeetRestriction.inclusion C I).op ⋙ P :=
  Functor.whiskerLeft (MeetRestriction.SemilatticeMeetRestriction.restriction C I).op
    (CechAugmentation.SemilatticeCechAugmentation.cone (Set.Iic I) ((MeetRestriction.SemilatticeMeetRestriction.inclusion C I).op ⋙ P))

def cone : (Functor.const Cᵒᵖ).obj (P.obj (op I)) ⟶ P :=
  meetCone C I P ≫ (MeetRestriction.SemilatticeMeetRestriction.iso C I P h).inv

theorem cone_comp : cone C I P h ≫ (MeetRestriction.SemilatticeMeetRestriction.iso C I P h).hom = meetCone C I P := by
  dsimp only [cone]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem app_comp (V : C) : (cone C I P h).app (op V) ≫
    P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op =
      P.map (homOfLE (inf_le_right : V ⊓ I ≤ I)).op :=
  congrArg (fun α => α.app (op V)) (cone_comp C I P h)

theorem self : (cone C I P h).app (op I) = 𝟙 (P.obj (op I)) := by
  let := h I
  apply (cancel_mono (P.map (homOfLE (inf_le_left : I ⊓ I ≤ I)).op)).mp
  exact (app_comp C I P h I).trans (Category.id_comp _).symm

variable (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

theorem factorization : η = (Functor.const Cᵒᵖ).map (η.app (op I)) ≫ cone C I P h := by
  apply (cancel_mono (MeetRestriction.SemilatticeMeetRestriction.iso C I P h).hom).mp
  rw [Category.assoc, cone_comp]
  apply NatTrans.ext
  funext V
  change η.app V ≫ P.map (homOfLE (inf_le_left : V.unop ⊓ I ≤ V.unop)).op =
    η.app (op I) ≫ P.map (homOfLE (inf_le_right : V.unop ⊓ I ≤ I)).op
  exact ((η.naturality (homOfLE (inf_le_left : V.unop ⊓ I ≤ V.unop)).op).symm.trans
    (Category.id_comp _)).trans
      ((η.naturality (homOfLE (inf_le_right : V.unop ⊓ I ≤ I)).op).symm.trans (Category.id_comp _)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone
