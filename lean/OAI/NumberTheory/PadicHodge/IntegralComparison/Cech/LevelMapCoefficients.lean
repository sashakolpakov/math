import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare

/-! # Level Map Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapCoefficients

noncomputable section

/-! The actual coefficient-transported Čech map commutes with a
further additive coefficient functor, with the canonical total isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (T : A ⥤ B) [T.Additive] (F : B ⥤ D) [F.Additive]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q)

theorem map : (F.mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map T U P Q a) ≫
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom =
    GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (T ⋙ F) U P
      (Q ⋙ F.mapHomologicalComplex (.up ℕ))
      (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) := by
  let FF := F.mapHomologicalComplex (.up ℕ)
  let CC := GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor (A := D) U
  let a' := Functor.whiskerRight a FF
  have hm := FF.map_comp (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom
    ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map a)
  have hn := GeometricComparison.CechCone.CoefficientNaturality.CechConeCoefficientNaturality.total F U a
  have hc := GeometricComparison.CechCone.CoefficientComposition.CechConeCoefficientComposition.total T F U P
  exact (congrArg (fun q => q ≫ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom) hm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => FF.map (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom ≫ q) hn).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ CC.map a') hc.symm))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapCoefficients
