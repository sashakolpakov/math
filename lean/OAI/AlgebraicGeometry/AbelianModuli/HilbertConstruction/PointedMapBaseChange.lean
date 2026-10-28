import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Pointed Map Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapBaseChange

noncomputable section

/-! Identity preservation is preserved and reflected by the canonical geometric comparisons of family pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem pointedMap_conjugate_iff {V : Scheme.{u}} {A B A' B' : Over V}
    [MonObj A] [MonObj B] [MonObj A'] [MonObj B']
    (e : A ≅ A') (d : B ≅ B') [IsMonHom e.hom] [IsMonHom d.hom] (f : A' ⟶ B') :
    η[A] ≫ (e.hom ≫ f ≫ d.inv) = η[B] ↔ η[A'] ≫ f = η[B'] := by
  rw [← Category.assoc η[A], IsMonHom.one_hom e.hom]
  constructor
  · intro h
    have H := congrArg (fun v => v ≫ d.hom) h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, IsMonHom.one_hom d.hom] using H
  · intro h
    rw [← Category.assoc, h, IsMonHom.one_hom d.inv]

theorem geometricFamilyMorphismBaseChange_pointed_iff {S : Scheme.{u}} {U T A B : Over S}
    [MonObj A] [MonObj B] (c : U ⟶ T)
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    η[(Over.pullback U.hom).obj A] ≫ Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f = η[(Over.pullback U.hom).obj B] ↔
      η[(Over.pullback c.left).obj ((Over.pullback T.hom).obj A)] ≫ (Over.pullback c.left).map f =
        η[(Over.pullback c.left).obj ((Over.pullback T.hom).obj B)] := by
  have := ParameterPullbackMonoidIso.singleParameterBaseChangeIso_isMonHom c A
  have := ParameterPullbackMonoidIso.singleParameterBaseChangeIso_isMonHom c B
  exact pointedMap_conjugate_iff (Single.ParameterBaseChange.singleParameterBaseChangeIso c A)
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c B) ((Over.pullback c.left).map f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapBaseChange
