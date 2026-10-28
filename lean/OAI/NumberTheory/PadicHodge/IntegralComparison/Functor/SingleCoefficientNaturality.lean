import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

/-! # Single Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientNaturality

noncomputable section

/-! The original single-degree total coordinates are natural in the
coefficient object, including the signed total flip. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive] {M N : C} (a : M ⟶ N) (c : ℕ)

def bicomplexMap : SingleTotal.bicomplex F M c ⟶ SingleTotal.bicomplex F N c :=
  (F.mapHomologicalComplex (.up ℕ)).map ((single C (.up ℕ) c).map a)

def totalMap : (SingleTotal.bicomplex F M c).total (.up ℕ) ⟶ (SingleTotal.bicomplex F N c).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap F a c) (.up ℕ)

omit [HasCoproducts D] in
@[reassoc]
theorem row_naturality :
    (bicomplexMap F a c).f c ≫ (SingleTotal.rowIso F N c).hom =
      (SingleTotal.rowIso F M c).hom ≫ F.map a := by
  change F.map (((single C (.up ℕ) c).map a).f c) ≫
      F.map (singleObjXSelf (.up ℕ) c N).hom =
    F.map (singleObjXSelf (.up ℕ) c M).hom ≫ F.map a
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  simp only [single_map_f_self, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
theorem homology_naturality (n : ℕ) :
    homologyMap (totalMap F a c) (n+c) ≫ (SingleTotal.homologyIso F N c n).hom =
      (SingleTotal.homologyIso F M c n).hom ≫ homologyMap (F.map a) n := by
  let b := bicomplexMap F a c
  let bf := GeometricComparison.TotalFlip.TotalFlipNaturality.flipped b
  have hf := congrArg (fun f => homologyMap f (n+c))
    (GeometricComparison.TotalFlip.TotalFlipNaturality.natural b)
  simp only [homologyMap_comp] at hf
  have hfi := CohomologyConcentrationNaturality.inverse_square _ _
    (homologyMapIso ((SingleTotal.bicomplex F M c).totalFlipIso (.up ℕ)) (n+c))
    (homologyMapIso ((SingleTotal.bicomplex F N c).totalFlipIso (.up ℕ)) (n+c)) hf
  have hs : homologyMap (HomologicalComplex₂.total.map bf (.up ℕ)) (n+c) ≫
        (AbelianSingleRowTotal.homologyIso (SingleTotal.bicomplex F N c).flip c (SingleTotal.off_degree F N c) n).hom =
      (AbelianSingleRowTotal.homologyIso (SingleTotal.bicomplex F M c).flip c (SingleTotal.off_degree F M c) n).hom ≫
        homologyMap (b.f c) n :=
    AbelianSingleRowTotal.homology_naturality c (SingleTotal.off_degree F M c) bf (SingleTotal.off_degree F N c) n
  have hr := congrArg (fun f => homologyMap f n) (row_naturality F a c)
  simp only [homologyMap_comp] at hr
  have hsr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hr
  simpa only [SingleTotal.homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom,
    Category.assoc, totalMap, b, bf] using
      DualComplexHomology.compose_squares _ _ _ _ _ _ _ hfi hsr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientNaturality
