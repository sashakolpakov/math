import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Homology Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyCoefficient

noncomputable section

/-! Exact coefficient change preserves the literal coefficient
coordinate of the homology of a single complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z r t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  {D : Type w} [Category.{z} D] [Abelian D] [HasCoproducts.{0} D]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology]

omit [HasCoproducts C] [HasCoproducts D] in
theorem homology_coordinate (S : ShortComplex C) :
    (S.map G).homologyπ ≫ (S.mapHomologyIso G).hom =
      (S.mapCyclesIso G).hom ≫ G.map S.homologyπ := by
  let h := S.leftHomologyData
  rw [h.mapHomologyIso_eq G, h.mapCyclesIso_eq G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, h.map G |>.homologyπ_comp_homologyIso_hom]
  change ((h.map G).cyclesIso.hom ≫ G.map h.π) ≫ G.map h.homologyIso.inv = _
  rw [Category.assoc, ← G.map_comp, h.π_comp_homologyIso_inv]
  rw [G.map_comp]

variable {B : Type r} [Category.{t} B] [Abelian B]
  (E : B ⥤ C) [E.Additive] (M : B) (c : ℕ)

omit [HasCoproducts C] [HasCoproducts D] in
theorem source :
    (((IntegralComparison.Functor.SingleEdge.source E M c).sc c).mapHomologyIso G).hom ≫
        G.map (IntegralComparison.Functor.SingleEdge.sourceIso E M c).hom =
      (IntegralComparison.Functor.SingleEdge.sourceIso (E ⋙ G) M c).hom := by
  let K := IntegralComparison.Functor.SingleEdge.source E M c
  let L := IntegralComparison.Functor.SingleEdge.source (E ⋙ G) M c
  apply (cancel_epi (L.homologyπ c)).mp
  have hp := homology_coordinate G (K.sc c)
  have hi := ShortComplex.mapCyclesIso_hom_iCycles (K.sc c) G
  have hs := IntegralComparison.Functor.SingleEdge.source_coordinate E M c
  have ht := IntegralComparison.Functor.SingleEdge.source_coordinate (E ⋙ G) M c
  calc
    _ = ((K.sc c).mapCyclesIso G).hom ≫ G.map (K.homologyπ c) ≫
        G.map (IntegralComparison.Functor.SingleEdge.sourceIso E M c).hom := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ G.map (IntegralComparison.Functor.SingleEdge.sourceIso E M c).hom) hp).trans
          (Category.assoc _ _ _))
    _ = ((K.sc c).mapCyclesIso G).hom ≫ G.map (K.iCycles c) ≫
        G.map (E.map (singleObjXSelf (.up ℕ) c M).hom) := by
      rw [← G.map_comp, hs, G.map_comp]
    _ = L.iCycles c ≫ G.map (E.map (singleObjXSelf (.up ℕ) c M).hom) := by
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hi)
    _ = _ := ht.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.HomologyCoefficient
