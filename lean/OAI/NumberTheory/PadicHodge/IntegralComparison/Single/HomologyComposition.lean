import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleEdge

/-! # Homology Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyComposition

noncomputable section

/-! The canonical coefficient coordinate of a single complex is
compatible with composing additive functors. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z r t
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  {B : Type r} [Category.{t} B] [Abelian B] [HasCoproducts.{0} B]
  (P : C ⥤ D) [P.Additive] (Q : D ⥤ B) [Q.Additive] (M : C) (c : ℕ)

abbrev map := (Q.mapHomologicalComplex (.up ℕ)).map
  ((singleMapHomologicalComplex P (.up ℕ) c).app M).hom

omit [HasCoproducts B] in
theorem coordinate :
    homologyMap (HomologyComposition.map P Q M c) c ≫ (Functor.SingleEdge.sourceIso Q (P.obj M) c).hom =
      (Functor.SingleEdge.sourceIso (P ⋙ Q) M c).hom := by
  let K := Functor.SingleEdge.source (P ⋙ Q) M c
  let L := Functor.SingleEdge.source Q (P.obj M) c
  let a : K ⟶ L := HomologyComposition.map P Q M c
  apply (cancel_epi (K.homologyπ c)).mp
  have hh := Functor.SingleEdge.source_coordinate Q (P.obj M) c
  have ht := Functor.SingleEdge.source_coordinate (P ⋙ Q) M c
  have hf : a.f c ≫ Q.map (singleObjXSelf (.up ℕ) c (P.obj M)).hom =
      Q.map (P.map (singleObjXSelf (.up ℕ) c M).hom) := by
    change Q.map (((singleMapHomologicalComplex P (.up ℕ) c).app M).hom.f c) ≫ _ = _
    rw [← Q.map_comp]
    congr 1
    have hx : ((singleMapHomologicalComplex P (.up ℕ) c).app M).hom.f c =
        P.map (singleObjXSelf (.up ℕ) c M).hom ≫ (singleObjXSelf (.up ℕ) c (P.obj M)).inv :=
      singleMapHomologicalComplex_hom_app_self P (.up ℕ) c M
    exact (congrArg (· ≫ (singleObjXSelf (.up ℕ) c (P.obj M)).hom) hx).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (P.map (singleObjXSelf (.up ℕ) c M).hom ≫ ·)
          (singleObjXSelf (.up ℕ) c (P.obj M)).inv_hom_id).trans (Category.comp_id _)))
  calc
    _ = cyclesMap a c ≫ L.homologyπ c ≫ (Functor.SingleEdge.sourceIso Q (P.obj M) c).hom := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Functor.SingleEdge.sourceIso Q (P.obj M) c).hom)
          (homologyπ_naturality a c)).trans (Category.assoc _ _ _))
    _ = cyclesMap a c ≫ L.iCycles c ≫ Q.map (singleObjXSelf (.up ℕ) c (P.obj M)).hom :=
      congrArg (cyclesMap a c ≫ ·) hh
    _ = K.iCycles c ≫ a.f c ≫ Q.map (singleObjXSelf (.up ℕ) c (P.obj M)).hom := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ Q.map (singleObjXSelf (.up ℕ) c (P.obj M)).hom)
          (cyclesMap_i a c)).trans (Category.assoc _ _ _))
    _ = _ := (congrArg (K.iCycles c ≫ ·) hf).trans ht.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyComposition
