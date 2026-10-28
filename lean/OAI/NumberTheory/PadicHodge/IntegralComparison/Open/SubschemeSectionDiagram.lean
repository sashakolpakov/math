import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex

/-! # Subscheme Section Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeSectionDiagram

noncomputable section

/-! A diagram of opens contained in one open subscheme has the same
actual section diagram there. The identification preserves both open
restriction and coefficient morphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {Y : Scheme.{u}} {C : Type v} [Category C]
  (F : C ⥤ Y.Opens) (V : Y.Opens) (hF : ∀ r, F.obj r ≤ V)

private abbrev sections (N : Y.Modules) : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N).obj

def opens : C ⥤ V.toScheme.Opens := F ⋙ Opens.map V.ι.base

include hF in
theorem image_eq (r : C) : V.ι ''ᵁ ((opens F V).obj r) = F.obj r := by
  change V.ι ''ᵁ (V.ι ⁻¹ᵁ F.obj r) = F.obj r
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr (hF r)]

def imageOpens : C ⥤ Y.Opens := opens F V ⋙ V.ι.opensFunctor

def coordinates (N : Y.Modules) :
    (opens F V).op ⋙ sections (N.restrict V.ι) ≅ (imageOpens F V).op ⋙ sections N :=
  NatIso.ofComponents
    (fun r => N.restrictAppIso V.ι ((opens F V).obj r.unop))
    (fun {_ _} a => N.map_restrictAppIso_hom V.ι ((opens F V).map a.unop).op)

def geometricIso (N : Y.Modules) : F.op ⋙ sections N ≅
    (imageOpens F V).op ⋙ sections N :=
  NatIso.ofComponents
    (fun r => (sections N).mapIso ((eqToIso (image_eq F V hF r.unop)).op))
    (fun {_ _} a => by
      change (sections N).map _ ≫ (sections N).map _ =
        (sections N).map _ ≫ (sections N).map _
      rw [← (sections N).map_comp, ← (sections N).map_comp]
      congr 1)

def iso (N : Y.Modules) : F.op ⋙ sections N ≅
    (opens F V).op ⋙ sections (N.restrict V.ι) :=
  geometricIso F V hF N ≪≫ (coordinates F V N).symm

variable (F₂ : C ⥤ Y.Opens) (hF₂ : ∀ r, F₂.obj r ≤ V) (α : F₂ ⟶ F)

def opensMap : opens F₂ V ⟶ opens F V := Functor.whiskerRight α (Opens.map V.ι.base)

def restriction (N : Y.Modules) : F.op ⋙ sections N ⟶ F₂.op ⋙ sections N :=
  Functor.whiskerRight (NatTrans.op α) (sections N)

theorem restriction_square (N : Y.Modules) :
    restriction F F₂ α N ≫ (iso F₂ V hF₂ N).hom =
      (iso F V hF N).hom ≫
        restriction (opens F V) (opens F₂ V) (opensMap F V F₂ α) (N.restrict V.ι) := by
  apply NatTrans.ext
  funext r
  change N.presheaf.map (α.app r.unop).op ≫
      (N.presheaf.map (eqToHom (image_eq F₂ V hF₂ r.unop)).op ≫
        (N.restrictAppIso V.ι ((opens F₂ V).obj r.unop)).inv) =
    (N.presheaf.map (eqToHom (image_eq F V hF r.unop)).op ≫
      (N.restrictAppIso V.ι ((opens F V).obj r.unop)).inv) ≫
        (N.restrict V.ι).presheaf.map ((opensMap F V F₂ α).app r.unop).op
  rw [Category.assoc, N.restrictAppIso_inv_map V.ι]
  simp only [← Category.assoc, ← N.presheaf.map_comp]
  congr 2

variable {N P : Y.Modules} (f : N ⟶ P)

def coefficientMap : F.op ⋙ sections N ⟶ F.op ⋙ sections P :=
  Functor.whiskerLeft F.op ((SheafOfModules.toSheaf Y.ringCatSheaf).map f).hom

theorem coefficient_square :
    coefficientMap F f ≫ (iso F V hF P).hom =
      (iso F V hF N).hom ≫
        coefficientMap (opens F V) ((Scheme.Modules.restrictFunctor V.ι).map f) := by
  apply NatTrans.ext
  funext r
  exact (((SheafOfModules.toSheaf Y.ringCatSheaf).map f).hom.naturality
    (eqToHom (image_eq F V hF r.unop)).op).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeSectionDiagram
