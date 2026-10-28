import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Ambient Open Factor Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientOpenFactorSections

noncomputable section

/-! Sections of an actual restriction-pushforward factor on inverse-image opens agree naturally with ambient sections on intersections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {X P : Scheme.{u}} (a : P ⟶ X) (B : P.Opens)

def ambientIntersectionOpenFunctor : X.Opens ⥤ P.Opens where
  obj V := a ⁻¹ᵁ V ⊓ B
  map i := homOfLE (inf_le_inf_right B (leOfHom ((Opens.map a.base).map i)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable (F : P.carrier.Sheaf AddCommGrpCat.{u})

def ambientOpenFactorSectionPresheaf : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Opens.map a.base).op ⋙ ((IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op B)).obj

def ambientOpenFactorSectionsIso :
    ambientOpenFactorSectionPresheaf a B F ≅
      (ambientIntersectionOpenFunctor a B).op ⋙ F.obj :=
  NatIso.ofComponents (fun V => Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F B (a ⁻¹ᵁ V.unop)) (by
    intro V W i
    let G : P.Opensᵒᵖ ⥤ AddCommGrpCat.{u} := F.obj
    change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
    exact (G.map_comp _ _).symm.trans
      ((G.congr_map (Subsingleton.elim _ _)).trans (G.map_comp _ _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientOpenFactorSections
