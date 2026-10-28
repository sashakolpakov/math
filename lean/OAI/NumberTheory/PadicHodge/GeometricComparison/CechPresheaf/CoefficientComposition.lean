import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalChain

/-! # Coefficient Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientComposition.CechPresheafCoefficientComposition

noncomputable section

/-! Successive additive coefficient changes agree with their composite
on the original finite Cech total of a presheaf complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uA vA uB vB uD vD
variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I) (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasCoproducts.{0} D] in
theorem bicomplex_iso :
    CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso (F ⋙ G) E hE K =
      NaturalTotalChain.NaturalTotalCoefficientComposition.bicomplexIso F G
        (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE K) (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G E hE (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K)) := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext q
  exact GeometricComparison.Finite.CechCoefficientComposition.FiniteCechCoefficientComposition.complexes F G E hE (K.X q)

theorem total_iso :
    (G.mapHomologicalComplex (.up ℕ)).mapIso (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE K) ≪≫
        CoefficientTotal.CechPresheafCoefficientTotal.totalIso G E hE (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K) = CoefficientTotal.CechPresheafCoefficientTotal.totalIso (F ⋙ G) E hE K := by
  have h := NaturalTotalChain.NaturalTotalCoefficientComposition.totalIso F G
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso F E hE K) (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G E hE (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K))
  rw [← bicomplex_iso F G E hE K] at h
  exact h

theorem hom :
    (G.mapHomologicalComplex (.up ℕ)).map (CoefficientTotal.CechPresheafCoefficientTotal.totalIso F E hE K).hom ≫
        (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G E hE (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F K)).hom = (CoefficientTotal.CechPresheafCoefficientTotal.totalIso (F ⋙ G) E hE K).hom :=
  congrArg Iso.hom (total_iso F G E hE K)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientComposition.CechPresheafCoefficientComposition
