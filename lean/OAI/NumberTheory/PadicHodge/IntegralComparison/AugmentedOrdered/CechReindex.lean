import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange

/-! # Cech Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex

noncomputable section

/-! Finite-product-preserving reindexing of the actual augmented
ordered Čech complex, including its empty-intersection coordinate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
  (P : Dᵒᵖ ⥤ A)

def componentIso (n : ℕ) : Cech.object U (r.op ⋙ P) n ≅ Cech.object (r.obj ∘ U) P n :=
  Pi.mapIso (fun a : Cech.Index ι n =>
    P.mapIso (PreservesProduct.iso r (fun j : Fin n => U (a.val j))).symm.op)

omit [Preadditive A] in
theorem component_hom_π (n : ℕ) (a : Cech.Index ι n) :
    (componentIso r U P n).hom ≫
        Pi.π (fun b : Cech.Index ι n => P.obj (op ((Cech.formal (r.obj ∘ U) n).obj b))) a =
      Pi.π (fun b : Cech.Index ι n => P.obj (op (r.obj ((Cech.formal U n).obj b)))) a ≫
        P.map (PreservesProduct.iso r (fun j : Fin n => U (a.val j))).inv.op :=
  Pi.mapIso_hom_π _ _

omit [Preadditive A] in
theorem coface_naturality (n : ℕ) (k : Fin (n + 1)) :
    Cech.coface U (r.op ⋙ P) n k ≫ (componentIso r U P (n + 1)).hom =
      (componentIso r U P n).hom ≫ Cech.coface (r.obj ∘ U) P n k := by
  apply AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
    (fun a : Cech.Index ι n => P.mapIso (PreservesProduct.iso r (fun j => U (a.val j))).symm.op)
    (fun a : Cech.Index ι (n + 1) => P.mapIso (PreservesProduct.iso r (fun j => U (a.val j))).symm.op)
    (fun a => a.delete k)
    (fun a => P.map (r.map ((Cech.face U n k).φ a)).op)
    (fun a => P.map ((Cech.face (r.obj ∘ U) n k).φ a).op)
  intro a
  change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
  exact (P.map_comp _ _).symm.trans
    ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

theorem differential_naturality (n : ℕ) :
    Cech.differential U (r.op ⋙ P) n ≫ (componentIso r U P (n + 1)).hom =
      (componentIso r U P n).hom ≫ Cech.differential (r.obj ∘ U) P n := by
  simp only [Cech.differential, comp_sum, sum_comp, comp_zsmul, zsmul_comp, coface_naturality]

def iso : Cech.complex U (r.op ⋙ P) ≅ Cech.complex (r.obj ∘ U) P :=
  HomologicalComplex.Hom.isoOfComponents (fun n => componentIso r U P n) (by
    intro n m h
    obtain rfl : m = n + 1 := h.symm
    dsimp only [Cech.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact (differential_naturality r U P n).symm)

theorem hom_f (n : ℕ) : (CechReindex.iso r U P).hom.f n = (componentIso r U P n).hom := rfl

theorem naturality {Q : Dᵒᵖ ⥤ A} (a : P ⟶ Q) :
    CechFunctor.complexMap U (Functor.whiskerLeft r.op a) ≫ (CechReindex.iso r U Q).hom =
      (CechReindex.iso r U P).hom ≫ CechFunctor.complexMap (r.obj ∘ U) a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.productIso_natural
    (fun b : Cech.Index ι n => P.mapIso (PreservesProduct.iso r (fun j => U (b.val j))).symm.op)
    (fun b : Cech.Index ι n => Q.mapIso (PreservesProduct.iso r (fun j => U (b.val j))).symm.op)
    id (fun b => a.app (op (r.obj ((Cech.formal U n).obj b))))
    (fun b => a.app (op ((Cech.formal (r.obj ∘ U) n).obj b)))
  intro b
  exact (a.naturality (PreservesProduct.iso r (fun j => U (b.val j))).inv.op).symm

def functorIso :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj r.op ⋙ CechFunctor.functor U ≅
      CechFunctor.functor (r.obj ∘ U) :=
  NatIso.ofComponents (fun P => CechReindex.iso r U P) (fun {_ _} a => CechReindex.naturality r U _ a)

def terminalIso : (r.op ⋙ P).obj (op (⊤_ C)) ≅ P.obj (op (⊤_ D)) :=
  P.mapIso (PreservesTerminal.iso r).symm.op

theorem zero :
    (CechReindex.iso r U P).hom.f 0 ≫ (CechZero.zeroIso (r.obj ∘ U) P).hom =
      (CechZero.zeroIso U (r.op ⋙ P)).hom ≫ (terminalIso r P).hom := by
  change (componentIso r U P 0).hom ≫
      (Pi.π (fun b : Cech.Index ι 0 => P.obj (op ((Cech.formal (r.obj ∘ U) 0).obj b))) CechZero.emptyIndex ≫
        P.map (CechZero.emptyProductMap (r.obj ∘ U) CechZero.emptyIndex).op) =
    (Pi.π (fun b : Cech.Index ι 0 => P.obj (op (r.obj ((Cech.formal U 0).obj b)))) CechZero.emptyIndex ≫
      P.map (r.map (CechZero.emptyProductMap U CechZero.emptyIndex)).op) ≫
        P.map (PreservesTerminal.iso r).inv.op
  rw [← Category.assoc, component_hom_π, Category.assoc, Category.assoc,
    ← P.map_comp, ← P.map_comp]
  exact congrArg (fun z =>
    Pi.π (fun b : Cech.Index ι 0 => P.obj (op (r.obj ((Cech.formal U 0).obj b)))) CechZero.emptyIndex ≫ P.map z)
      (Subsingleton.elim _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex
