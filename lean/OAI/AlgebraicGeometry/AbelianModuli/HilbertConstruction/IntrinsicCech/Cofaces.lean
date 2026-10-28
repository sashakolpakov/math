/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechDifferential.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains

/-! # Cofaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cofaces

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

variable {T : Type u} [TopologicalSpace T]
variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u}
variable (U : ι → Opens T) (n : ℕ)

theorem cechCoface_eq (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj F).δ k =
      Pi.lift (fun i : Fin (n + 2) → ι =>
        Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          F.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  rfl

theorem cechDifferential_eq :
    ((cechComplexFunctor U).obj F).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj F).δ k := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj F).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ n).trans rfl

theorem addCommGrp_sum_apply_finset {A B : AddCommGrpCat} {κ : Type*}
    (s : Finset κ) (f : κ → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        AddCommGrpCat.hom_add_apply, ih]

theorem addCommGrp_sum_apply {A B : AddCommGrpCat} {κ : Type*}
    [Fintype κ] (f : κ → (A ⟶ B)) (x : A) :
    (∑ i, f i) x = ∑ i, f i x :=
  addCommGrp_sum_apply_finset Finset.univ f x

/-- A Cech coface restricts the component indexed by the tuple with its `k`th entry
deleted to the full tuple intersection. -/
theorem nativeCechCoface_apply (x : ((cechComplexFunctor U).obj F).X n)
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    Cochains.cechCochainAddEquiv F U (n + 1)
        (((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj F).δ k x) i =
      F.map (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
        (Cochains.cechCochainAddEquiv F U n x
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  have hout := Cochains.cechCochainAddEquiv_apply F U (n + 1)
    (((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj F).δ k x) i
  have hin := Cochains.cechCochainAddEquiv_apply F U n x
    (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  rw [hout, hin, cechCoface_eq]
  exact ConcreteCategory.congr_hom
    (Pi.lift_comp_π (fun i : Fin (n + 2) → ι =>
      Pi.π (fun j : Fin (n + 1) → ι =>
        F.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        F.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) i) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cofaces
