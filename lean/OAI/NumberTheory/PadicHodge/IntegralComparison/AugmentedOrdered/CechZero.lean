import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.Cech

/-! # Cech Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero

noncomputable section

/-! Degree zero of the supported ordered Čech complex is the
actual ambient section object. Its first differential is restriction
to the chosen opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]

def emptyIndex : Cech.Index ι 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩

theorem index_zero_eq (a : Cech.Index ι 0) : a = emptyIndex := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

def emptyProductMap (a : Cech.Index ι 0) : ⊤_ C ⟶ (Cech.formal U 0).obj a :=
  Pi.lift (fun i : Fin 0 => Fin.elim0 i)

variable (P : Cᵒᵖ ⥤ D)

def zeroIso : Cech.object U P 0 ≅ P.obj (op (⊤_ C)) where
  hom := Pi.π (fun a : Cech.Index ι 0 => P.obj (op ((Cech.formal U 0).obj a))) emptyIndex ≫
    P.map (emptyProductMap U emptyIndex).op
  inv := Pi.lift (fun a : Cech.Index ι 0 =>
    P.map (terminal.from ((Cech.formal U 0).obj a)).op)
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    rw [index_zero_eq a]
    simp only [Category.assoc, Pi.lift_comp_π]
    rw [← P.map_comp, ← op_comp]
    have h : terminal.from ((Cech.formal U 0).obj emptyIndex) ≫ emptyProductMap U emptyIndex =
        𝟙 ((Cech.formal U 0).obj emptyIndex) := Subsingleton.elim _ _
    rw [h, op_id, P.map_id, Category.comp_id]
    simp only [Category.id_comp]
    rfl
  inv_hom_id := by
    rw [← Category.assoc]
    erw [Pi.lift_comp_π]
    rw [← P.map_comp, ← op_comp]
    have h : emptyProductMap U emptyIndex ≫ terminal.from ((Cech.formal U 0).obj emptyIndex) =
        𝟙 (⊤_ C) := Subsingleton.elim _ _
    rw [h, op_id, P.map_id]

omit [Preadditive D] in
theorem zeroIso_inv_π (a : Cech.Index ι 0) :
    (zeroIso U P).inv ≫
      Pi.π (fun b : Cech.Index ι 0 => P.obj (op ((Cech.formal U 0).obj b))) a =
        P.map (terminal.from ((Cech.formal U 0).obj a)).op :=
  Pi.lift_comp_π _ _

omit [Preadditive D] in
theorem zeroIso_inv_coface_π (a : Cech.Index ι 1) :
    (zeroIso U P).inv ≫ Cech.coface U P 0 0 ≫
      Pi.π (fun b : Cech.Index ι 1 => P.obj (op ((Cech.formal U 1).obj b))) a =
        P.map (terminal.from ((Cech.formal U 1).obj a)).op := by
  change (zeroIso U P).inv ≫
    (Pi.lift (fun b : Cech.Index ι 1 =>
      Pi.π (fun c : Cech.Index ι 0 => P.obj (op ((Cech.formal U 0).obj c))) (b.delete 0) ≫
        P.map ((Cech.face U 0 0).φ b).op)) ≫
      Pi.π (fun b : Cech.Index ι 1 => P.obj (op ((Cech.formal U 1).obj b))) a = _
  rw [Pi.lift_comp_π, ← Category.assoc, zeroIso_inv_π, ← P.map_comp, ← op_comp]
  congr 1

theorem zeroIso_inv_differential_π (a : Cech.Index ι 1) :
    (zeroIso U P).inv ≫ Cech.differential U P 0 ≫
      Pi.π (fun b : Cech.Index ι 1 => P.obj (op ((Cech.formal U 1).obj b))) a =
        P.map (terminal.from ((Cech.formal U 1).obj a)).op := by
  simpa only [Cech.differential, Nat.reduceAdd, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_zsmul] using
    zeroIso_inv_coface_π U P a

omit [Preadditive D] in
theorem zeroIso_naturality {Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) :
    (((FormalCoproduct.evalOp C D).map f).app (op (Cech.formal U 0))) ≫ (zeroIso U Q).hom =
      (zeroIso U P).hom ≫ f.app (op (⊤_ C)) := by
  change Limits.Pi.map (fun a : Cech.Index ι 0 => f.app (op ((Cech.formal U 0).obj a))) ≫
      (Pi.π (fun a : Cech.Index ι 0 => Q.obj (op ((Cech.formal U 0).obj a))) emptyIndex ≫
        Q.map (emptyProductMap U emptyIndex).op) = _
  rw [← Category.assoc, Pi.map_π, Category.assoc]
  simpa only [zeroIso, Category.assoc] using congrArg (fun a =>
    Pi.π (fun b : Cech.Index ι 0 => P.obj (op ((Cech.formal U 0).obj b))) emptyIndex ≫ a)
      (f.naturality (emptyProductMap U emptyIndex).op).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
