import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FunctorBaseChange

/-! # Diagram Open Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagramOpenIso

noncomputable section

/-! A natural isomorphism transports open chart arrows between scheme diagrams over a base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem overDiagram_open_of_iso
    {S : Scheme.{u}} {J : Type v} [Category.{w} J] {F G : J ⥤ Over S} (e : F ≅ G)
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left] {i j : J} (h : i ⟶ j) :
    IsOpenImmersion (F.map h).left := by
  have : IsIso (e.hom.app i).left := (Over.forget S).map_isIso (e.hom.app i)
  have : IsIso (e.inv.app j).left := (Over.forget S).map_isIso (e.inv.app j)
  have he : F.map h = e.hom.app i ≫ G.map h ≫ e.inv.app j := by
    rw [← e.hom.naturality_assoc, e.hom_inv_id_app, Category.comp_id]
  have he' : (F.map h).left = (e.hom.app i).left ≫ (G.map h).left ≫ (e.inv.app j).left :=
    congrArg (fun f => f.left) he
  have hc : IsOpenImmersion ((e.hom.app i).left ≫ (G.map h).left ≫ (e.inv.app j).left) := inferInstance
  exact (congrArg (fun k : (F.obj i).left ⟶ (F.obj j).left => IsOpenImmersion k) he').mpr hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagramOpenIso
