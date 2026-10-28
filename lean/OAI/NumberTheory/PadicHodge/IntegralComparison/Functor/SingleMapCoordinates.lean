import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

/-! # Single Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates

noncomputable section

/-! The original single-degree total coordinates commute with any
genuine bicomplex map whose retained row is specified. In particular,
they commute with natural transformations of coefficient functors. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z r s
section General
variable {C : Type u} [Category.{v} C] [Abelian C]
  {C' : Type w} [Category.{z} C'] [Abelian C']
  {D : Type r} [Category.{s} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive]
  (G : C' ⥤ CochainComplex D ℕ) [G.Additive]
  (M : C) (N : C') (c : ℕ)
  (b : SingleTotal.bicomplex F M c ⟶ SingleTotal.bicomplex G N c) (a : F.obj M ⟶ G.obj N)
  (hrow : b.f c ≫ (SingleTotal.rowIso G N c).hom = (SingleTotal.rowIso F M c).hom ≫ a)

include hrow in
theorem comparison (n : ℕ) :
    homologyMap (HomologicalComplex₂.total.map b (.up ℕ)) (n+c) ≫
        (SingleTotal.homologyIso G N c n).hom =
      (SingleTotal.homologyIso F M c n).hom ≫ homologyMap a n := by
  let bf := GeometricComparison.TotalFlip.TotalFlipNaturality.flipped b
  have hf := congrArg (fun f => homologyMap f (n+c))
    (GeometricComparison.TotalFlip.TotalFlipNaturality.natural b)
  simp only [homologyMap_comp] at hf
  have hfi := CohomologyConcentrationNaturality.inverse_square _ _
    (homologyMapIso ((SingleTotal.bicomplex F M c).totalFlipIso (.up ℕ)) (n+c))
    (homologyMapIso ((SingleTotal.bicomplex G N c).totalFlipIso (.up ℕ)) (n+c)) hf
  have hs : homologyMap (HomologicalComplex₂.total.map bf (.up ℕ)) (n+c) ≫
        (AbelianSingleRowTotal.homologyIso (SingleTotal.bicomplex G N c).flip c (SingleTotal.off_degree G N c) n).hom =
      (AbelianSingleRowTotal.homologyIso (SingleTotal.bicomplex F M c).flip c (SingleTotal.off_degree F M c) n).hom ≫
        homologyMap (b.f c) n :=
    AbelianSingleRowTotal.homology_naturality c (SingleTotal.off_degree F M c) bf (SingleTotal.off_degree G N c) n
  have hr := congrArg (fun f => homologyMap f n) hrow
  simp only [homologyMap_comp] at hr
  have hsr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hr
  simpa only [SingleTotal.homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom,
    Category.assoc, bf] using
      DualComplexHomology.compose_squares _ _ _ _ _ _ _ hfi hsr
end General

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  (F G : C ⥤ CochainComplex D ℕ) [F.Additive] [G.Additive]
  (η : F ⟶ G) (M : C) (c : ℕ)

def map : SingleTotal.bicomplex F M c ⟶ SingleTotal.bicomplex G M c :=
  (NatTrans.mapHomologicalComplex η (.up ℕ)).app ((single C (.up ℕ) c).obj M)

omit [HasCoproducts D] in
theorem row : (SingleMapCoordinates.map F G η M c).f c ≫ (SingleTotal.rowIso G M c).hom =
    (SingleTotal.rowIso F M c).hom ≫ η.app M := by
  change η.app (((single C (.up ℕ) c).obj M).X c) ≫ G.map (singleObjXSelf (.up ℕ) c M).hom =
    F.map (singleObjXSelf (.up ℕ) c M).hom ≫ η.app M
  exact (η.naturality (singleObjXSelf (.up ℕ) c M).hom).symm

theorem naturality (n : ℕ) :
    homologyMap (HomologicalComplex₂.total.map (SingleMapCoordinates.map F G η M c) (.up ℕ)) (n+c) ≫
        (SingleTotal.homologyIso G M c n).hom =
      (SingleTotal.homologyIso F M c n).hom ≫ homologyMap (η.app M) n :=
  comparison F G M M c (SingleMapCoordinates.map F G η M c) (η.app M) (row F G η M c) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates
