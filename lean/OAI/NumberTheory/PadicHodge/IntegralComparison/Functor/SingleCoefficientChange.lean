import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ColumnCoefficientCoordinates

/-! # Single Coefficient Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientChange

noncomputable section

/-! Exact coefficient change commutes with the original functorial
single-degree total coordinates, including the total-flip sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z r s
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  {E : Type r} [Category.{s} E] [Abelian E] [HasCoproducts.{0} E]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive]
  (G : D ⥤ E) [G.Additive] [G.PreservesHomology] (M : C) (c : ℕ)

local instance finiteBiproducts : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts

abbrev mappedFunctor : C ⥤ CochainComplex E ℕ := F ⋙ G.mapHomologicalComplex (.up ℕ)

abbrev totalIso :=
  AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (SingleTotal.bicomplex F M c)

theorem comparison (n : ℕ) :
    homologyMap (totalIso F G M c).inv (n+c) ≫
        (SingleTotal.homologyIso (mappedFunctor F G) M c n).hom ≫
          (((F.obj M).sc n).mapHomologyIso G).hom =
      ((((SingleTotal.bicomplex F M c).total (.up ℕ)).sc (n+c)).mapHomologyIso G).hom ≫
        G.map (SingleTotal.homologyIso F M c n).hom := by
  let B := SingleTotal.bicomplex F M c
  let hB := SingleTotal.off_degree F M c
  let BG := Single.ColumnCoefficientCoordinates.mapped G B
  let hBG := Single.ColumnCoefficientCoordinates.support G B c hB
  let iB := Single.ColumnCycleCoordinates.homologyIso B c hB n
  let iBG := Single.ColumnCycleCoordinates.homologyIso BG c hBG n
  let row := (SingleTotal.rowIso F M c).hom
  have hc := Single.ColumnCoefficientCoordinates.homology G B c hB n
  have hr : homologyMap ((G.mapHomologicalComplex (.up ℕ)).map row) n ≫
        (((F.obj M).sc n).mapHomologyIso G).hom =
      (((B.X c).sc n).mapHomologyIso G).hom ≫ G.map (homologyMap row n) :=
    ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor D (.up ℕ) n).map row) G
  have hs : (SingleTotal.homologyIso F M c n).hom = iB.hom ≫ homologyMap row n := by
    simp only [SingleTotal.homologyIso, iB, Single.ColumnCycleCoordinates.homologyIso,
      Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom, B, row, Category.assoc]
  have ht : (SingleTotal.homologyIso (mappedFunctor F G) M c n).hom =
      iBG.hom ≫ homologyMap ((G.mapHomologicalComplex (.up ℕ)).map row) n := by
    simp only [SingleTotal.homologyIso, iBG, Single.ColumnCycleCoordinates.homologyIso,
      Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom, Category.assoc]
    rfl
  rw [hs, ht]
  change homologyMap (totalIso F G M c).inv (n+c) ≫
      (iBG.hom ≫ homologyMap ((G.mapHomologicalComplex (.up ℕ)).map row) n) ≫
        (((F.obj M).sc n).mapHomologyIso G).hom =
    (((B.total (.up ℕ)).sc (n+c)).mapHomologyIso G).hom ≫
      G.map (iB.hom ≫ homologyMap row n)
  calc
    _ = (homologyMap (totalIso F G M c).inv (n+c) ≫ iBG.hom ≫
        (((B.X c).sc n).mapHomologyIso G).hom) ≫ G.map (homologyMap row n) := by
      simp only [Category.assoc]
      rw [hr]
    _ = ((((B.total (.up ℕ)).sc (n+c)).mapHomologyIso G).hom ≫ G.map iB.hom) ≫
        G.map (homologyMap row n) := congrArg (· ≫ G.map (homologyMap row n)) hc
    _ = _ := by rw [G.map_comp, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientChange
