import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.TotalQuasiIso

/-! # Augmented Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechRefinement

noncomputable section

/-! The original augmented ordered refinement is a quasi-isomorphism
with additive-group coefficients whenever its full nonempty refinement is. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})

private abbrev integral := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv

local instance : integral.{u}.Additive := by
  let : (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.functor.Additive := by
    change (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).Additive
    infer_instance
  exact (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse_additive

def tailIso : Cochain.TailQuasiIso.tail
    ((integral.{u}.mapHomologicalComplex (.up ℕ)).obj
      (AugmentedOrdered.Cech.complex U P)) ≅
    (integral.{u}.mapHomologicalComplex (.up ℕ)).obj
      (OrderedCech.Projection.complex U P) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    obtain rfl : i + 1 = j := h
    change integral.{u}.map ((OrderedCech.Projection.complex U P).d i (i + 1)) ≫ 𝟙 _ =
      𝟙 _ ≫ integral.{u}.map ((AugmentedOrdered.Cech.complex U P).d (i + 1) (i + 1 + 1))
    simp only [Category.comp_id, Category.id_comp]
    congr 1
    simp only [AugmentedOrdered.Cech.complex,
      OrderedCech.Projection.complex, CochainComplex.of_d,
      OrderedCech.Projection.differential])

theorem tail_map : Cochain.TailQuasiIso.map
    ((integral.{u}.mapHomologicalComplex (.up ℕ)).map
      (AugmentedOrdered.CechRefinement.map U V r P)) =
    (tailIso U P).hom ≫
      (integral.{u}.mapHomologicalComplex (.up ℕ)).map
        (OrderedCech.Refinement.map U V r P) ≫ (tailIso V P).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  change integral.{u}.map ((AugmentedOrdered.CechRefinement.map U V r P).f (n + 1)) =
    𝟙 _ ≫ integral.{u}.map ((OrderedCech.Refinement.map U V r P).f n) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, AugmentedOrdered.CechRefinement.map_f_succ]

theorem quasiIso [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P)] :
    QuasiIso (AugmentedOrdered.CechRefinement.map U V r P) := by
  let : IsIso ((AugmentedOrdered.CechRefinement.map U V r P).f 0) := by
    rw [AugmentedOrdered.CechRefinement.map_f_zero]
    infer_instance
  let : QuasiIso (OrderedCech.Refinement.map U V r P) :=
    OrderedCech.Refinement.quasiIso U V r P
  have h : QuasiIso ((integral.{u}.mapHomologicalComplex (.up ℕ)).map
      (AugmentedOrdered.CechRefinement.map U V r P)) := by
    let : IsIso (((integral.{u}.mapHomologicalComplex (.up ℕ)).map
        (AugmentedOrdered.CechRefinement.map U V r P)).f 0) := by
      change IsIso (integral.{u}.map ((AugmentedOrdered.CechRefinement.map U V r P).f 0))
      infer_instance
    apply Cochain.TailQuasiIso.quasiIso
    rw [tail_map]
    infer_instance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ integral.{u}).mp h

theorem total_quasiIso (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ)
    (hK : ∀ q, QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (K.X q))) :
    QuasiIso (AugmentedOrdered.CechRefinementTotal.totalMap U V r K) := by
  apply TotalQuasiIso.quasiIso
  intro q
  let := hK q
  exact quasiIso U V r (K.X q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechRefinement
