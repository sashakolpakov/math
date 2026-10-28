import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates

/-! # Single Coefficient Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientIso

noncomputable section

/-! Exact coefficient change followed by a specified natural
isomorphism preserves the original single-total coordinate isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z r s
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  {E : Type r} [Category.{s} E] [Abelian E] [HasCoproducts.{0} E]
  (F : C ⥤ CochainComplex D ℕ) [F.Additive]
  (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
  (H : C ⥤ CochainComplex E ℕ) [H.Additive]
  (e : SingleCoefficientChange.mappedFunctor F G ≅ H)
  (M : C) (c : ℕ)

abbrev bicomplexIso :=
  (NatIso.mapHomologicalComplex e (.up ℕ)).app ((single C (.up ℕ) c).obj M)

def totalIso := (SingleCoefficientChange.totalIso F G M c).symm ≪≫
  HomologicalComplex₂.total.mapIso (bicomplexIso F G H e M c) (.up ℕ)

def homologyIso (n : ℕ) :=
  ((((SingleTotal.bicomplex F M c).total (.up ℕ)).sc (n+c)).mapHomologyIso G).symm ≪≫
    homologyMapIso (totalIso F G H e M c) (n+c)

def coefficientIso (n : ℕ) :=
  (((F.obj M).sc n).mapHomologyIso G).symm ≪≫ homologyMapIso (e.app M) n

theorem comparison (n : ℕ) :
    (homologyIso F G H e M c n).hom ≫ (SingleTotal.homologyIso H M c n).hom =
      G.map (SingleTotal.homologyIso F M c n).hom ≫
        (coefficientIso F G H e M n).hom := by
  have hc := SingleCoefficientChange.comparison F G M c n
  have he := SingleMapCoordinates.naturality
    (SingleCoefficientChange.mappedFunctor F G) H e.hom M c n
  have hc' :
      homologyMap (SingleCoefficientChange.totalIso F G M c).inv (n+c) ≫
        (SingleTotal.homologyIso (SingleCoefficientChange.mappedFunctor F G) M c n).hom =
      ((((SingleTotal.bicomplex F M c).total (.up ℕ)).sc (n+c)).mapHomologyIso G).hom ≫
        G.map (SingleTotal.homologyIso F M c n).hom ≫
          (((F.obj M).sc n).mapHomologyIso G).inv := by
    apply (cancel_mono (((F.obj M).sc n).mapHomologyIso G).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  simp only [homologyIso, totalIso, coefficientIso, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_hom, homologyMap_comp, Category.assoc]
  erw [he]
  erw [← Category.assoc (homologyMap (SingleCoefficientChange.totalIso F G M c).inv (n+c)), hc']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientIso
