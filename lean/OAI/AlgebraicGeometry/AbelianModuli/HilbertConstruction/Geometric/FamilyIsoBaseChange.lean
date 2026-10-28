import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Family Iso Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FamilyIsoBaseChange

noncomputable section

/-! Isomorphisms of pulled-back families admit geometric base change to the original family pullbacks, preserving the group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {U T : Over S} {A B : Over S}

def geometricFamilyIsoBaseChange (c : U ⟶ T)
    (e : (Over.pullback T.hom).obj A ≅ (Over.pullback T.hom).obj B) :
    (Over.pullback U.hom).obj A ≅ (Over.pullback U.hom).obj B :=
  Single.ParameterBaseChange.singleParameterBaseChangeIso c A ≪≫ (Over.pullback c.left).mapIso e ≪≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso c B).symm

theorem geometricFamilyIsoBaseChange_hom (c : U ⟶ T)
    (e : (Over.pullback T.hom).obj A ≅ (Over.pullback T.hom).obj B) :
    (geometricFamilyIsoBaseChange c e).hom = MorphismBaseChange.geometricFamilyMorphismBaseChange c e.hom := rfl

theorem geometricFamilyIsoBaseChange_isMonHom [MonObj A] [MonObj B] (c : U ⟶ T)
    (e : (Over.pullback T.hom).obj A ≅ (Over.pullback T.hom).obj B) [IsMonHom e.hom] :
    IsMonHom (geometricFamilyIsoBaseChange c e).hom :=
  (ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff c e.hom).mpr inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FamilyIsoBaseChange
