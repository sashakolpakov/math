import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSectionAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.PresheafEvaluation

/-! # De Rham Coefficient Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex

noncomputable section

/-!
# IntegralComparison: the native global de Rham presheaf complex with the original crystalline coefficients
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]

def coefficients : ModuleCat.{u} k ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ModuleCat.restrictScalars (WittVector.constantCoeff (p := p) (R := k)) ⋙
    EtaleZero.DeRham.Comparison.coefficientFunctor p k

instance coefficients_additive : (coefficients p k).Additive := by
  dsimp only [coefficients]
  infer_instance

variable (X : Over (Spec (CommRingCat.of k)))

def presheaves : (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k) ⥤
    (X.left.Opensᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  (Functor.whiskeringRight _ _ _).obj (coefficients p k)

instance presheaves_additive : (presheaves p k X).Additive := by
  dsimp only [presheaves]
  infer_instance

def complex : CochainComplex
    (X.left.Opensᵒᵖ ⥤ ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  ((presheaves p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X)

def evaluationIso (U : X.left.Opens) :
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (complex p k X) ≅
    ((coefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U))) :=
  ((coefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (GeometricComparison.DeRham.PresheafEvaluation.DeRhamPresheafEvaluation.complexIso k X U)

variable (C : Type u) [CommRing C] [Algebra k C]
  (g : Spec (CommRingCat.of C) ⟶ X.left) [IsOpenImmersion g]
  (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k C)))

def chartIso : ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) g.opensRange).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (complex p k X) ≅ EtaleZero.DeRham.Comparison.deRhamComplex p k C :=
  evaluationIso p k X g.opensRange ≪≫
    ((coefficients p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (Affine.ChartSectionAlgebra.complexIso k C X g hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex
