import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations

/-! # Pointed Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PointedBaseChange

noncomputable section

/-! Geometric base change of an identity-preserving map preserves the identity, through the actual monoid comparison isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem geometricFamilyMorphismBaseChange_preserves_unit
    {S : Scheme.{u}} {U T : Over S} (c : U ⟶ T) {A B : Over S} [MonObj A] [MonObj B]
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (hf : η[(Over.pullback T.hom).obj A] ≫ f = η[(Over.pullback T.hom).obj B]) :
    η[(Over.pullback U.hom).obj A] ≫ MorphismBaseChange.geometricFamilyMorphismBaseChange c f =
      η[(Over.pullback U.hom).obj B] := by
  have := ParameterPullbackMonoidIso.singleParameterBaseChangeIso_isMonHom c A
  have := ParameterPullbackMonoidIso.singleParameterBaseChangeIso_isMonHom c B
  have hfm : η[(Over.pullback c.left).obj ((Over.pullback T.hom).obj A)] ≫
      (Over.pullback c.left).map f = η[(Over.pullback c.left).obj ((Over.pullback T.hom).obj B)] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback c.left) f).mpr (congrArg (Over.pullback c.left).map hf)
  change η[(Over.pullback U.hom).obj A] ≫
    ((Single.ParameterBaseChange.singleParameterBaseChangeIso c A).hom ≫ (Over.pullback c.left).map f ≫
      (Single.ParameterBaseChange.singleParameterBaseChangeIso c B).inv) = _
  rw [← Category.assoc, IsMonHom.one_hom, ← Category.assoc, hfm, IsMonHom.one_hom]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PointedBaseChange
