import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraPresheafScalars
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # De Rham Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamGlobal

noncomputable section

/-!
# IntegralComparison: the native global de Rham complex with its Frobenius structure-sheaf action
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))

def presheafComplex : CochainComplex (PresheafOfModules.{u} X.left.ringCatSheaf.obj) ℕ :=
  DeRhamPresheaf.complex k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)

def formsIso (n : ℕ) :
    (AlgebraPresheafScalars.functor k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)).obj ((presheafComplex k X).X n) ≅
      OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n :=
  NatIso.ofComponents (fun U => DeRhamComplex.formsIso k
    ((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj U) n)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro ω
        rfl)

def underlyingIso :
    ((AlgebraPresheafScalars.functor k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (presheafComplex k X) ≅ OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X :=
  HomologicalComplex.Hom.isoOfComponents (formsIso k X)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      change (formsIso k X i).hom ≫ (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X).d i (i + 1) =
        (AlgebraPresheafScalars.functor k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)).map
          ((presheafComplex k X).d i (i + 1)) ≫ (formsIso k X (i + 1)).hom
      dsimp only [presheafComplex, DeRhamPresheaf.complex, OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply NatTrans.ext
      funext U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      rfl)

def sheafification : PresheafOfModules.{u} X.left.ringCatSheaf.obj ⥤ X.left.Modules :=
  PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)

instance sheafification_additive : (DeRhamGlobal.sheafification k X).Additive where
  map_add {M N f g} := by
    apply (SheafOfModules.toSheaf.{u} X.left.ringCatSheaf).map_injective
    exact (PresheafOfModules.toPresheaf X.left.ringCatSheaf.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X.left) AddCommGrpCat).map_add

def complex : CochainComplex X.left.Modules ℕ :=
  ((DeRhamGlobal.sheafification k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (presheafComplex k X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamGlobal
