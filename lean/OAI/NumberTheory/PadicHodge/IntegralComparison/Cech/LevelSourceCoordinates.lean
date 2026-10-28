import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapCoefficients

/-! # Level Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelSourceCoordinates

noncomputable section

/-! A chosen literal source coordinate for a Čech cone remains exact
under additive coefficient change. -/

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
  (M : CochainComplex A ℕ) (e : GeometricComparison.CechCone.Total.CechConeTotal.total U P ⟶ M)
  (m : (T.mapHomologicalComplex (.up ℕ)).obj M ⟶ GeometricComparison.CechCone.Total.CechConeTotal.total U Q)
  (hm : (T.mapHomologicalComplex (.up ℕ)).map e ≫ m =
    GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map T U P Q a)

include hm in
theorem map :
    ((F.mapHomologicalComplex (.up ℕ)).map ((T.mapHomologicalComplex (.up ℕ)).map e) ≫
      (F.mapHomologicalComplex (.up ℕ)).map m) ≫
        (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom =
    GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (T ⋙ F) U P
      (Q ⋙ F.mapHomologicalComplex (.up ℕ))
      (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) :=
  (congrArg (fun q => q ≫ (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U Q).hom)
    (((F.mapHomologicalComplex (.up ℕ)).map_comp _ _).symm.trans
      (congrArg (F.mapHomologicalComplex (.up ℕ)).map hm))).trans
        (LevelMapCoefficients.map T F U P Q a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelSourceCoordinates
