import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Total Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalExtension

noncomputable section

/-! Finite totalization and extension commute with the same actual additive functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

local instance : K.HasTotal (.up ℕ) := TotalExists.hasTotal_of_finiteCoproducts K
local instance : (TotalComplexFunctor.mapBicomplex F K).HasTotal (.up ℕ) :=
  TotalExists.hasTotal_of_finiteCoproducts (TotalComplexFunctor.mapBicomplex F K)

def finiteTotalExtensionIso :
    ((TotalComplexFunctor.mapBicomplex F K).total (.up ℕ)).extend (ComplexShape.embeddingUpIntGE 0) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj
        ((K.total (.up ℕ)).extend (ComplexShape.embeddingUpIntGE 0)) :=
  ((ComplexShape.embeddingUpIntGE 0).extendFunctor D).mapIso (TotalFunctor.finiteTotalComparisonIso F K) ≪≫
    (Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0) (K.total (.up ℕ))).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalExtension
