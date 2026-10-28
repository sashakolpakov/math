import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip

/-! # Single Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

noncomputable section

/-! Applying an additive complex-valued functor to one coefficient
degree gives the original coefficient complex with its actual shift.
The identification is natural in transformations of those functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive] (M : C) (c : ℕ)

def bicomplex : HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  (F.mapHomologicalComplex (.up ℕ)).obj ((single C (.up ℕ) c).obj M)

omit [HasCoproducts.{0} D] in
theorem off_degree (p q : ℕ) (hq : q ≠ c) :
    IsZero (((bicomplex F M c).flip.X p).X q) :=
  (HomologicalComplex.eval D (.up ℕ) p).map_isZero
    (F.map_isZero (isZero_single_obj_X (.up ℕ) c M q hq))

def rowIso : (bicomplex F M c).X c ≅ F.obj M :=
  F.mapIso (singleObjXSelf (.up ℕ) c M)

def homologyIso (n : ℕ) :
    ((bicomplex F M c).total (.up ℕ)).homology (n + c) ≅ (F.obj M).homology n :=
  (homologyMapIso ((bicomplex F M c).totalFlipIso (.up ℕ)) (n + c)).symm ≪≫
    AbelianSingleRowTotal.homologyIso (bicomplex F M c).flip c (off_degree F M c) n ≪≫
      homologyMapIso (rowIso F M c) n

variable {F} {G : C ⥤ CochainComplex D ℕ} [G.Additive] (φ : F ⟶ G)

def bicomplexMap : bicomplex F M c ⟶ bicomplex G M c :=
  (φ.mapHomologicalComplex (.up ℕ)).app ((single C (.up ℕ) c).obj M)

def totalMap : (bicomplex F M c).total (.up ℕ) ⟶ (bicomplex G M c).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap M c φ) (.up ℕ)

omit [HasCoproducts D] in
theorem row_naturality :
    (bicomplexMap M c φ).f c ≫ (rowIso G M c).hom =
      (rowIso F M c).hom ≫ φ.app M :=
  (φ.naturality (singleObjXSelf (.up ℕ) c M).hom).symm

theorem homology_naturality (n : ℕ) :
    homologyMap (totalMap M c φ) (n + c) ≫ (homologyIso G M c n).hom =
      (homologyIso F M c n).hom ≫ homologyMap (φ.app M) n := by
  let b := bicomplexMap M c φ
  let bf := GeometricComparison.TotalFlip.TotalFlipNaturality.flipped b
  have hf := congrArg (fun f => homologyMap f (n + c))
    (GeometricComparison.TotalFlip.TotalFlipNaturality.natural b)
  simp only [homologyMap_comp] at hf
  have hfi := CohomologyConcentrationNaturality.inverse_square _ _
    (homologyMapIso ((bicomplex F M c).totalFlipIso (.up ℕ)) (n + c))
    (homologyMapIso ((bicomplex G M c).totalFlipIso (.up ℕ)) (n + c)) hf
  have hs : homologyMap (HomologicalComplex₂.total.map bf (.up ℕ)) (n + c) ≫
        (AbelianSingleRowTotal.homologyIso (bicomplex G M c).flip c (off_degree G M c) n).hom =
      (AbelianSingleRowTotal.homologyIso (bicomplex F M c).flip c (off_degree F M c) n).hom ≫
        homologyMap (b.f c) n :=
    AbelianSingleRowTotal.homology_naturality c (off_degree F M c) bf (off_degree G M c) n
  have hr := congrArg (fun f => homologyMap f n) (row_naturality M c φ)
  simp only [homologyMap_comp] at hr
  have hsr := DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hr
  simpa only [homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom,
    Category.assoc, totalMap, b, bf] using
      DualComplexHomology.compose_squares _ _ _ _ _ _ _ hfi hsr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal
