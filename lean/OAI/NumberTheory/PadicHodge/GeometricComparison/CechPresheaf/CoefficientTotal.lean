import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor

/-! # Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal

noncomputable section

/-! Additive coefficient change commutes with original finite Cech totals
of presheaf-valued complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v a b d e
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I) (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

def presheaves : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ B) := (Functor.whiskeringRight Cᵒᵖ A B).obj F

instance presheaves_additive : (presheaves (C := C) F).Additive := by
  dsimp only [presheaves]
  infer_instance

def bicomplex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).obj K

def mappedComplex : CochainComplex (Cᵒᵖ ⥤ B) ℕ :=
  ((presheaves (C := C) F).mapHomologicalComplex (.up ℕ)).obj K

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (bicomplex E K) ≅
    bicomplex E (mappedComplex F K) :=
  (NatIso.mapHomologicalComplex (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.iso F E hE) (.up ℕ)).app K

def totalIso : (F.mapHomologicalComplex (.up ℕ)).obj ((bicomplex E K).total (.up ℕ)) ≅
    (bicomplex E (mappedComplex F K)).total (.up ℕ) :=
  (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (bicomplex E K)).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso F E hE K) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal
