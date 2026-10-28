import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSmallIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.IsoOpens

/-! # Principal Family Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family

noncomputable section

/-! Original principal affine-frame families of two finite-level models
are isomorphic over one coefficient category. The projection square
uses exactly the prescribed base-frame isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X₁.hom] [Smooth X₂.hom]
  (Y : Over (Spec (CommRingCat.of k)))
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)

local notation "Q₁" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X₁ Y f₁ hp₁) U₁
local notation "Q₂" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X₂ Y f₂ hp₂) U₂
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X₁.left U₁

variable (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
  (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)

def reindex : C ⥤ PrincipalFrame.Index X₂.left U₂ :=
  CrystallinePrincipal.Iso.coefficients p k Y e

def frames : C ⥤ AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k Y :=
  reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e ⋙
    PrincipalFrame.frames p k n X₂ Y f₂ hp₂ U₂

def iso : frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e ≅
    PrincipalFrame.frames p k n X₁ Y f₁ hp₁ U₁ :=
  Functor.isoWhiskerLeft (reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
      (PrincipalSmallIso.diagramIso p k n X₂ Y f₂ hp₂ U₂) ≪≫
    CrystallinePrincipal.Iso.diagramIso p k Y e ≪≫
      (PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).symm

def projection (r : C) : (frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).obj r ⟶ Q₂ :=
  PrincipalFrame.projection p k n X₂ Y f₂ hp₂ U₂
    ((reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).obj r)

theorem inverse_projection (r : C) :
    (PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).inv.app r ≫
      PrincipalFrame.projection p k n X₁ Y f₁ hp₁ U₁ r =
        AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k Y Q₁ r := by
  rw [← PrincipalFrame.map_projection p k n X₁ Y f₁ hp₁ U₁ r]
  exact (PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).app r |>.inv_hom_id_assoc _

theorem projection_square (r : C) :
    (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom.app r ≫
      PrincipalFrame.projection p k n X₁ Y f₁ hp₁ U₁ r =
        projection p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e r ≫ e.hom := by
  change (PrincipalFrame.map p k n X₂ Y f₂ hp₂ U₂
    ((reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).obj r) ≫
      CrystallinePrincipal.Iso.map p k Y e r ≫
        (PrincipalSmallIso.diagramIso p k n X₁ Y f₁ hp₁ U₁).inv.app r) ≫ _ = _
  rw [Category.assoc, Category.assoc, inverse_projection,
    CrystallinePrincipal.Iso.map_projection, ← Category.assoc]
  exact congrArg (fun z => z ≫ e.hom)
    (PrincipalFrame.map_projection p k n X₂ Y f₂ hp₂ U₂
      ((reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).obj r))

theorem special_opens_eq (r : C) :
    ((frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).obj r).immersion.opensRange =
      ((PrincipalFrame.frames p k n X₁ Y f₁ hp₁ U₁).obj r).immersion.opensRange :=
  CrystallinePrincipal.IsoOpens.opens_eq p k Y ((iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).app r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family
