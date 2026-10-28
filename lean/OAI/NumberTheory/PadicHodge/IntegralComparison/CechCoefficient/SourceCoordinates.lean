import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LevelMapComposition

/-! # Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SourceCoordinates

noncomputable section

/-! Splitting a coefficient functor gives the precise source isomorphism
for a Čech cone map written in another total-complex coordinate system. -/

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
  (M : CochainComplex A ℕ) (e : GeometricComparison.CechCone.Total.CechConeTotal.total U P ≅ M)

def sourceIso : (T.mapHomologicalComplex (.up ℕ)).obj M ≅
    GeometricComparison.CechCone.Total.CechConeTotal.total U (P ⋙ T.mapHomologicalComplex (.up ℕ)) :=
  ((T.mapHomologicalComplex (.up ℕ)).mapIso e).symm ≪≫
    GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P

variable (m : ((T ⋙ F).mapHomologicalComplex (.up ℕ)).obj M ⟶
    GeometricComparison.CechCone.Total.CechConeTotal.total U Q)
  (hm : ((T ⋙ F).mapHomologicalComplex (.up ℕ)).map e.hom ≫ m =
    GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (T ⋙ F) U P Q a)

include hm in
theorem map_eq : m =
    (F.mapHomologicalComplex (.up ℕ)).map (sourceIso T U P M e).hom ≫
      GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map F U
        (P ⋙ T.mapHomologicalComplex (.up ℕ)) Q a := by
  calc
    m = ((T ⋙ F).mapHomologicalComplex (.up ℕ)).map e.inv ≫
        (((T ⋙ F).mapHomologicalComplex (.up ℕ)).map e.hom ≫ m) :=
      (Category.id_comp m).symm.trans
        ((congrArg (fun q => q ≫ m)
          (((T ⋙ F).mapHomologicalComplex (.up ℕ)).mapIso e).inv_hom_id.symm).trans
            (Category.assoc _ _ _))
    _ = ((T ⋙ F).mapHomologicalComplex (.up ℕ)).map e.inv ≫
        ((F.mapHomologicalComplex (.up ℕ)).map
          (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom ≫
            GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map F U
              (P ⋙ T.mapHomologicalComplex (.up ℕ)) Q a) :=
      congrArg (fun q => ((T ⋙ F).mapHomologicalComplex (.up ℕ)).map e.inv ≫ q)
        (hm.trans (Cech.LevelMapComposition.map T F U P Q a))
    _ = _ :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map F U
          (P ⋙ T.mapHomologicalComplex (.up ℕ)) Q a)
            (((F.mapHomologicalComplex (.up ℕ)).map_comp
              ((T.mapHomologicalComplex (.up ℕ)).map e.inv)
              (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom).symm))

omit m hm in
theorem map_composite (K : CochainComplex D ℕ)
    (r : ((T ⋙ F).mapHomologicalComplex (.up ℕ)).obj M ⟶ K)
    (t : K ⟶ GeometricComparison.CechCone.Total.CechConeTotal.total U Q)
    (h : (((T ⋙ F).mapHomologicalComplex (.up ℕ)).map e.hom ≫ r) ≫ t =
      GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (T ⋙ F) U P Q a) :
    r ≫ t = (F.mapHomologicalComplex (.up ℕ)).map (sourceIso T U P M e).hom ≫
      GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map F U
        (P ⋙ T.mapHomologicalComplex (.up ℕ)) Q a :=
  map_eq T F U P Q a M e (r ≫ t) ((Category.assoc _ _ _).symm.trans h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SourceCoordinates
