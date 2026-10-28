import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinement

/-! # Cech Refinement Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementQuasiIso

noncomputable section

/-! Fixing ambient sections and refining the nonempty cover preserves
the actual supported Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  {R : Type v} [Ring R] (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R)

def tailIso : Cochain.TailQuasiIso.tail (Cech.complex U P) ≅ OrderedCech.Projection.complex U P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    obtain rfl : i + 1 = j := h
    simp only [Cochain.TailQuasiIso.tail, Cech.complex, OrderedCech.Projection.complex,
      CochainComplex.of_d, OrderedCech.Projection.differential,
      Iso.refl_hom, Category.comp_id, Category.id_comp])

theorem tail_map : Cochain.TailQuasiIso.map (CechRefinement.map U V r P) =
    (tailIso U P).hom ≫ OrderedCech.Refinement.map U V r P ≫ (tailIso V P).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  change (CechRefinement.map U V r P).f (n + 1) =
    𝟙 _ ≫ (OrderedCech.Refinement.map U V r P).f n ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, CechRefinement.map_f_succ]

theorem quasiIso [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P)] :
    QuasiIso (CechRefinement.map U V r P) := by
  let : IsIso ((CechRefinement.map U V r P).f 0) := by
    rw [CechRefinement.map_f_zero]
    infer_instance
  apply Cochain.TailQuasiIso.quasiIso
  let : QuasiIso (OrderedCech.Refinement.map U V r P) :=
    OrderedCech.Refinement.quasiIso U V r P
  rw [tail_map]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementQuasiIso
