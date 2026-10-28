import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor

/-! # Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex

noncomputable section

/-! Finite-limit-preserving changes of open diagrams preserve the
actual ordered Cech complex and its projection from all tuples. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
  (P : Dᵒᵖ ⥤ A)

def iso : Projection.complex U (r.op ⋙ P) ≅
    Projection.complex (r.obj ∘ U) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AugmentedOrdered.CechReindex.componentIso r U P (n+1)) (by
      intro n m h
      obtain rfl : m = n+1 := h.symm
      dsimp only [Projection.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      exact (AugmentedOrdered.CechReindex.differential_naturality r U P (n+1)).symm)

theorem hom_f (n : ℕ) : (Reindex.iso r U P).hom.f n =
    (AugmentedOrdered.CechReindex.componentIso r U P (n+1)).hom := rfl

theorem naturality {Q : Dᵒᵖ ⥤ A} (a : P ⟶ Q) :
    OrderedCech.Functor.Projection.complexMap U (Functor.whiskerLeft r.op a) ≫ (Reindex.iso r U Q).hom =
      (Reindex.iso r U P).hom ≫ OrderedCech.Functor.Projection.complexMap (r.obj ∘ U) a := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun z => z.f (n+1)) (AugmentedOrdered.CechReindex.naturality r U P a)

def functorIso :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj r.op ⋙ OrderedCech.Functor.Projection.functor U ≅
      OrderedCech.Functor.Projection.functor (r.obj ∘ U) :=
  NatIso.ofComponents (fun P => Reindex.iso r U P) (fun {_ _} a => naturality r U _ a)

theorem projection :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso r U P).hom ≫ Projection.map (r.obj ∘ U) P =
      Projection.map U (r.op ⋙ P) ≫ (Reindex.iso r U P).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  symm
  change Projection.mapF U (r.op ⋙ P) n ≫
      (AugmentedOrdered.CechReindex.componentIso r U P (n+1)).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.componentIso r U P ⦋n⦌).hom ≫
      Projection.mapF (r.obj ∘ U) P n
  have h := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
    (fun a : Fin (n+1) → ι => P.mapIso (PreservesProduct.iso r (U ∘ a)).symm.op)
    (fun a : Projection.Index (ι := ι) n =>
      P.mapIso (PreservesProduct.iso r (U ∘ a.val)).symm.op)
    (fun a => a.val) (fun _ => 𝟙 _) (fun _ => 𝟙 _)
    (by intro a; simp only [Category.id_comp, Category.comp_id])
  simp only [Category.comp_id] at h
  dsimp only [Projection.mapF, Cech.TupleRestrictionFunctor.projection,
    NonemptyCechDifferential.projection, AugmentedOrdered.CechReindex.componentIso,
    AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.componentIso]
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex
