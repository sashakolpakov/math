import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientTransformation
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap

/-! # Total Functor Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare

noncomputable section

/-! A square of additive coefficient functors and complex diagrams
commutes with the original finite Cech total coefficient isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The coefficient square on any indexing category, before taking a Čech total. -/
def diagramMapDirect {I : Type*} [Category I]
    {A : Type*} [Category A] [Preadditive A]
    {B : Type*} [Category B] [Preadditive B]
    {D : Type*} [Category D] [Preadditive D]
    (T : A ⥤ B) [T.Additive] (S : A ⥤ D) [S.Additive]
    (S' : B ⥤ D) [S'.Additive]
    (P : I ⥤ CochainComplex A ℕ) (Q : I ⥤ CochainComplex B ℕ)
    (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S') :
    P ⋙ S.mapHomologicalComplex (.up ℕ) ⟶ Q ⋙ S'.mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerLeft P (b.mapHomologicalComplex (.up ℕ)) ≫
    Functor.whiskerRight a (S'.mapHomologicalComplex (.up ℕ))

universe u v w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (T : A ⥤ B) [T.Additive] (S : A ⥤ D) [S.Additive] (S' : B ⥤ D) [S'.Additive]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S')

def diagramMap : P ⋙ S.mapHomologicalComplex (.up ℕ) ⟶ Q ⋙ S'.mapHomologicalComplex (.up ℕ) :=
  diagramMapDirect T S S' P Q a b

def map : (S.mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total U P) ⟶
    (S'.mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total U Q) :=
  (b.mapHomologicalComplex (.up ℕ)).app (Total.CechConeTotal.total U P) ≫
    (S'.mapHomologicalComplex (.up ℕ)).map (TotalLevelMap.CechConeTotalLevelMap.map T U P Q a)

theorem natural : CechConeTotalFunctorSquare.map T S S' U P Q a b ≫ (TotalCoefficient.CechConeTotalCoefficient.totalIso S' U Q).hom =
    (TotalCoefficient.CechConeTotalCoefficient.totalIso S U P).hom ≫
      (TotalFunctor.CechConeTotalFunctor.functor U).map (diagramMap T S S' P Q a b) := by
  let SS := S'.mapHomologicalComplex (.up ℕ)
  let CC := TotalFunctor.CechConeTotalFunctor.functor (A := D) U
  let a' := Functor.whiskerRight a SS
  let b' := Functor.whiskerLeft P (b.mapHomologicalComplex (.up ℕ))
  have hA : SS.map (TotalLevelMap.CechConeTotalLevelMap.map T U P Q a) ≫
      (TotalCoefficient.CechConeTotalCoefficient.totalIso S' U Q).hom =
    (TotalCoefficient.CechConeTotalCoefficient.totalIso (T ⋙ S') U P).hom ≫ CC.map a' := by
    have hm := SS.map_comp (TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom
      ((TotalFunctor.CechConeTotalFunctor.functor U).map a)
    have hn := CoefficientNaturality.CechConeCoefficientNaturality.total S' U a
    have hc := CoefficientComposition.CechConeCoefficientComposition.total T S' U P
    exact (congrArg (fun q => q ≫ (TotalCoefficient.CechConeTotalCoefficient.totalIso S' U Q).hom) hm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => SS.map (TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom ≫ q) hn).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ CC.map a') hc.symm))))
  have hb := CoefficientTransformation.CechConeCoefficientTransformation.total S (T ⋙ S') b U P
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (b.mapHomologicalComplex (.up ℕ)).app (Total.CechConeTotal.total U P) ≫ q) hA).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ CC.map a') hb).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun q => (TotalCoefficient.CechConeTotalCoefficient.totalIso S U P).hom ≫ q) (CC.map_comp b' a').symm)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare
