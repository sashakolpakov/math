import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamGlobal

/-! # De Rham Sheaf Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamSheafIso

noncomputable section

/-!
# IntegralComparison: the original global de Rham sheaf complex is the underlying Frobenius module complex
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))

def sheafificationIso (K : CochainComplex (PresheafOfModules.{u} X.left.ringCatSheaf.obj) ℕ) :
    ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (((AlgebraSheafScalars.presheaves k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
    ((AlgebraSheafScalars.functor k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((DeRhamGlobal.sheafification k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => AlgebraSheafificationScalars.objectIso k X (K.X i))
      (fun i j _ => (AlgebraSheafificationScalars.naturality k X (K.d i j)).symm)

def iso :
    ((AlgebraSheafScalars.functor k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (DeRhamGlobal.complex k X) ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex k X :=
  (sheafificationIso k X (DeRhamGlobal.presheafComplex k X)).symm ≪≫
      ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k)).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso (DeRhamGlobal.underlyingIso k X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamSheafIso
