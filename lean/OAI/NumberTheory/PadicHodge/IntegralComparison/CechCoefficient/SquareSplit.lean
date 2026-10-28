import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapComposition

/-! # Square Split -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareSplit

noncomputable section

/-! A normalized coefficient square splits its source coefficient
functor before specializing to a native section functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z' w'' z'' w''' z'''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  {E : Type w'''} [Category.{z'''} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  (T : A ⥤ B) [T.Additive] (L : A ⥤ E) [L.Additive]
  (V : E ⥤ D) [V.Additive] (F : B ⥤ D) [F.Additive]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : L ⋙ V ⟶ T ⋙ F)
  (m : ((L ⋙ V).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U P) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U Q))
  (θ : P ⋙ (L ⋙ V).mapHomologicalComplex (.up ℕ) ⟶ Q ⋙ F.mapHomologicalComplex (.up ℕ))
  (hm : m = GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T (L ⋙ V) F U P Q a b)
  (hθ : GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.diagramMap T (L ⋙ V) F P Q a b = θ)

include hm hθ in
theorem natural : m ≫ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom =
    (V.mapHomologicalComplex (.up ℕ)).map
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso L U P).hom ≫
      GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map V U (P ⋙ L.mapHomologicalComplex (.up ℕ))
        (Q ⋙ F.mapHomologicalComplex (.up ℕ)) θ :=
  (SquareNormalization.natural T (L ⋙ V) F U P Q a b m θ hm hθ).trans
    (Cech.LevelMapComposition.map L V U P (Q ⋙ F.mapHomologicalComplex (.up ℕ)) θ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareSplit
