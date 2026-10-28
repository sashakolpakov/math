import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Forms

noncomputable section

/-! The preserved algebraic forms are the usual exterior Kähler form sheaves in every degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

variable (A : Type) [CommRing A] [Algebra ℂ A]

def exteriorFormsEquiv (n : ℕ) : Algebraic.Forms.Form A n ≃ₗ[ℂ] ⋀[A]^n Ω[A⁄ℂ] :=
  (NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter.formsEquiv A n).trans
    (Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.coordinateFormsEquiv ℂ (CommAlgCat.of ℂ A) n)

theorem exteriorFormsEquiv_symbol (n : ℕ) (a : Fin (n + 1) → A) :
    exteriorFormsEquiv A n (Algebraic.Forms.formSymbol A a) =
      a 0 • exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D ℂ A (a i.succ)) := by
  change Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior ℂ A n
    (NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter.to62 A n (Algebraic.Forms.formSymbol A a)) = _
  rw [NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter.to62_symbol]
  exact Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol ℂ A (a 0) (Fin.tail a)

theorem exteriorFormsEquiv_naturality {B : Type} [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (n : ℕ) (a : Algebraic.Forms.Form A n) :
    exteriorFormsEquiv B n (Algebraic.Forms.pullback f n a) =
      Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.ofHom f) n (exteriorFormsEquiv A n a) := by
  change Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior ℂ B n
    (NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter.to62 B n (Algebraic.Forms.pullback f n a)) = _
  rw [NumberTheory.PadicHodge.GeometricComparison.Forms.Adapter.FormsAdapter.to62_pullback]
  exact Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.toExterior_natural (CommAlgCat.ofHom f) n _

end

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def exteriorFormPresheafIso (n : ℕ) : Algebraic.Sheaves.formPresheaf X n ≅
    Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsPresheaf ℂ X n :=
  NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter.formPresheafIso X n ≪≫
    Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsPresheafIso ℂ X n

def exteriorFormSheafIso (n : ℕ) : (Algebraic.Sheaves.algebraicDeRhamSheafComplex X).X n ≅
    Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsSheaf ℂ X n :=
  ((HomologicalComplex.eval _ _ n).mapIso (NumberTheory.PadicHodge.GeometricComparison.SheafFormsAdapter.FormsAdapter.sheafComplexIso X)) ≪≫
    Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsSheafIso ℂ X n

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

theorem affineExteriorForms_finite [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Module.Finite Γ(X.left, U) (⋀[Γ(X.left, U)]^n Ω[Γ(X.left, U)⁄ℂ]) := by
  have : Algebra.FiniteType ℂ Γ(X.left, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType X.hom U hU
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Forms
