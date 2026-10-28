import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Parameter Pullback Monoid Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

noncomputable section

/-! The geometric comparison of parameter pullbacks preserves the actual monoid structures, so conjugating by it preserves and reflects homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {U T : Over S} (c : U ⟶ T)

def singleParameterBaseChangeMonIso (A : Over S) [MonObj A] :
    Mon.mk ((Over.pullback U.hom).obj A) ≅
      Mon.mk ((Over.pullback c.left).obj ((Over.pullback T.hom).obj A)) :=
  (Functor.mapMonNatIso (ParameterPullbackNaturality.singleParameterBaseChangeNatIso c)).app (Mon.mk A) ≪≫
    (Functor.mapMonCompIso (F := Over.pullback T.hom) (G := Over.pullback c.left)).app (Mon.mk A)

theorem singleParameterBaseChangeIso_isMonHom (A : Over S) [MonObj A] :
    IsMonHom (Single.ParameterBaseChange.singleParameterBaseChangeIso c A).hom := by
  have h : IsMonHom (singleParameterBaseChangeMonIso c A).hom.hom := inferInstance
  change IsMonHom ((Single.ParameterBaseChange.singleParameterBaseChangeIso c A).hom ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

theorem monoidHom_conjugate_iff {V : Scheme.{u}} {A B A' B' : Over V}
    [MonObj A] [MonObj B] [MonObj A'] [MonObj B']
    (e : A ≅ A') (d : B ≅ B') [IsMonHom e.hom] [IsMonHom d.hom] (f : A' ⟶ B') :
    IsMonHom (e.hom ≫ f ≫ d.inv) ↔ IsMonHom f := by
  constructor
  · intro h
    have : IsMonHom (e.inv ≫ (e.hom ≫ f ≫ d.inv) ≫ d.hom) := inferInstance
    simpa only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id] using this
  · intro h
    infer_instance

theorem geometricFamilyMorphismBaseChange_isMonHom_iff {A B : Over S} [MonObj A] [MonObj B]
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    IsMonHom (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f) ↔ IsMonHom ((Over.pullback c.left).map f) := by
  have := singleParameterBaseChangeIso_isMonHom c A
  have := singleParameterBaseChangeIso_isMonHom c B
  exact monoidHom_conjugate_iff (Single.ParameterBaseChange.singleParameterBaseChangeIso c A)
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c B) ((Over.pullback c.left).map f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso
