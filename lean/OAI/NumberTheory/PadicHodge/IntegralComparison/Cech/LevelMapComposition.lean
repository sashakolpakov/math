import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition

/-! # Level Map Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapComposition

noncomputable section

/-! The native level map for a composite coefficient functor factors
through the actual source Čech coefficient isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (T : A ⥤ B) [T.Additive] (F : B ⥤ D) [F.Additive]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex D ℕ)
  (a : P ⋙ (T ⋙ F).mapHomologicalComplex (.up ℕ) ⟶ Q)

theorem map : GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (T ⋙ F) U P Q a =
    (F.mapHomologicalComplex (.up ℕ)).map
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom ≫
      GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map F U
        (P ⋙ T.mapHomologicalComplex (.up ℕ)) Q a :=
  (congrArg (fun e => e ≫ (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map a)
    (GeometricComparison.CechCone.CoefficientComposition.CechConeCoefficientComposition.total T F U P)).trans (Category.assoc _ _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapComposition
