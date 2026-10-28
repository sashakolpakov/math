import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare

/-! # Square Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareNormalization

noncomputable section

/-! Normalize both presentations of an actual coefficient square
before specializing its Čech total compatibility. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (T : A ⥤ B) [T.Additive] (S : A ⥤ D) [S.Additive] (F : B ⥤ D) [F.Additive]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ F)
  (m : (S.mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U P) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechCone.Total.CechConeTotal.total U Q))
  (θ : P ⋙ S.mapHomologicalComplex (.up ℕ) ⟶ Q ⋙ F.mapHomologicalComplex (.up ℕ))
  (hm : m = GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T S F U P Q a b)
  (hθ : GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.diagramMap T S F P Q a b = θ)

include hm hθ in
theorem natural : m ≫ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom =
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P).hom ≫
      (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map θ :=
  (congrArg (fun q => q ≫ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom) hm).trans
    ((GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.natural T S F U P Q a b).trans
      (congrArg (fun q => (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P).hom ≫
        (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map q) hθ))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareNormalization
