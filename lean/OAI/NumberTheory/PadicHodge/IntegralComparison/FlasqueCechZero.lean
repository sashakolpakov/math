import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechDifferential
import OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeTupleIntersection
import OAI.NumberTheory.PadicHodge.GeometricComparison.LargeModuleAt
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Flasque Cech Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechZero

noncomputable section

/-! Every native Čech zero cocycle of a flasque module sheaf extends
to a global section, even when the family does not cover the space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v w
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R))
  {ι : Type} (U : ι → Opens X)

abbrev tupleOpen (a : Fin 1 → ι) : Opens X := ∏ᶜ (U ∘ a)
abbrev C := (NonemptyCechNerve.complexFunctor U).obj F.obj
abbrev π (a : Fin 1 → ι) := NonemptyCechDifferential.projection U F.obj 0 a

private theorem append_delete_zero (a b : Fin 1 → ι) :
    Fin.append a b ∘ (0 : Fin 2).succAbove = b := by
  funext i
  fin_cases i
  rfl

private theorem append_delete_one (a b : Fin 1 → ι) :
    Fin.append a b ∘ (1 : Fin 2).succAbove = a := by
  funext i
  fin_cases i
  rfl

private theorem projection_restriction_eq (a b : Fin 1 → ι) (hab : a = b)
    (T : Opens X) (f : T ⟶ tupleOpen X U a) (g : T ⟶ tupleOpen X U b) :
    π R X F U a ≫ F.obj.map f.op = π R X F U b ≫ F.obj.map g.op := by
  subst b
  rw [Subsingleton.elim f g]

theorem compatible (x : (FlasqueCechZero.C R X F U).X 0) (hx : (FlasqueCechZero.C R X F U).d 0 1 x = 0) :
    TopCat.Presheaf.IsCompatible F.obj (tupleOpen X U) (fun a => π R X F U a x) := by
  intro a b
  let t := Fin.append a b
  have ht : (∏ᶜ (U ∘ t)) = tupleOpen X U a ⊓ tupleOpen X U b := by
    have he : U ∘ t = Fin.append (U ∘ a) (U ∘ b) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [t, Function.comp_apply, Fin.append_left, Fin.append_right]
    rw [he]
    exact SemilatticeTupleIntersection.product_append (U ∘ a) (U ∘ b)
  let e : (∏ᶜ (U ∘ t)) ≅ tupleOpen X U a ⊓ tupleOpen X U b := eqToIso ht
  apply (ModuleCat.mono_iff_injective (F.obj.mapIso e.op).hom).mp inferInstance
  have hd := ConcreteCategory.congr_hom
    (NonemptyCechDifferential.differential_projection U F.obj 0 t) x
  have hzero : (NonemptyCechDifferential.projection U F.obj 1 t)
      ((FlasqueCechZero.C R X F U).d 0 1 x) = 0 := by rw [hx, map_zero]
  have hdiff :
      (F.obj.map (NonemptyCechDifferential.faceMap U 0 0 t).op)
        (NonemptyCechDifferential.projection U F.obj 0 (t ∘ (0 : Fin 2).succAbove) x) =
      (F.obj.map (NonemptyCechDifferential.faceMap U 0 1 t).op)
        (NonemptyCechDifferential.projection U F.obj 0 (t ∘ (1 : Fin 2).succAbove) x) := by
    have h := hd.symm.trans hzero
    change (∑ i : Fin 2, (-1 : ℤ)^i.val •
      (NonemptyCechDifferential.projection U F.obj 0 (t ∘ i.succAbove) ≫
        F.obj.map (NonemptyCechDifferential.faceMap U 0 i t).op)).hom x = 0 at h
    rw [Fin.sum_univ_two] at h
    simpa only [ Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_zsmul, neg_smul, neg_one_zsmul, ModuleCat.hom_add, ModuleCat.hom_zsmul, ModuleCat.hom_sub, ModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, neg_one_zsmul,
      ConcreteCategory.comp_apply, ← sub_eq_add_neg, sub_eq_zero] using h
  have hleft : (F.obj.mapIso e.op).hom
      (F.obj.map (homOfLE inf_le_left).op (π R X F U a x)) =
      (F.obj.map (NonemptyCechDifferential.faceMap U 0 1 t).op)
        (NonemptyCechDifferential.projection U F.obj 0 (t ∘ (1 : Fin 2).succAbove) x) := by
    change (((π R X F U a ≫ F.obj.map (homOfLE inf_le_left).op) ≫
      (F.obj.mapIso e.op).hom).hom x) =
      ((NonemptyCechDifferential.projection U F.obj 0 (t ∘ (1 : Fin 2).succAbove) ≫
        F.obj.map (NonemptyCechDifferential.faceMap U 0 1 t).op).hom x)
    apply ConcreteCategory.congr_hom _ x
    change (π R X F U a ≫ F.obj.map (homOfLE inf_le_left).op) ≫ F.obj.map e.hom.op = _
    rw [Category.assoc, ← F.obj.map_comp]
    exact projection_restriction_eq R X F U a _ (append_delete_one a b).symm _
      _ (NonemptyCechDifferential.faceMap U 0 1 t)
  have hright : (F.obj.mapIso e.op).hom
      (F.obj.map (homOfLE inf_le_right).op (π R X F U b x)) =
      (F.obj.map (NonemptyCechDifferential.faceMap U 0 0 t).op)
        (NonemptyCechDifferential.projection U F.obj 0 (t ∘ (0 : Fin 2).succAbove) x) := by
    change (((π R X F U b ≫ F.obj.map (homOfLE inf_le_right).op) ≫
      (F.obj.mapIso e.op).hom).hom x) =
      ((NonemptyCechDifferential.projection U F.obj 0 (t ∘ (0 : Fin 2).succAbove) ≫
        F.obj.map (NonemptyCechDifferential.faceMap U 0 0 t).op).hom x)
    apply ConcreteCategory.congr_hom _ x
    change (π R X F U b ≫ F.obj.map (homOfLE inf_le_right).op) ≫ F.obj.map e.hom.op = _
    rw [Category.assoc, ← F.obj.map_comp]
    exact projection_restriction_eq R X F U b _ (append_delete_zero a b).symm _
      _ (NonemptyCechDifferential.faceMap U 0 0 t)
  exact hleft.trans (hdiff.symm.trans hright.symm)

theorem exists_global [TopCat.Presheaf.IsFlasque (X := X) F.obj]
    (x : (FlasqueCechZero.C R X F U).X 0) (hx : (FlasqueCechZero.C R X F U).d 0 1 x = 0) :
    ∃ s : F.obj.obj (op ⊤), ∀ a : Fin 1 → ι,
      F.obj.map (homOfLE (le_top : tupleOpen X U a ≤ ⊤)).op s = π R X F U a x := by
  let : HasLimitsOfSize.{v, v} (ModuleCat.{max u v w} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v w, u}
  let : PreservesLimitsOfSize.{v, v} (forget (ModuleCat.{max u v w} R)) :=
    ModuleCat.forget_preservesLimitsOfSize.{v, v, max u v w, u}
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing (C := ModuleCat.{max u v w} R) (X := X) F (tupleOpen X U) (fun a => π R X F U a x)
    (compatible R X F U x hx)
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective
    (F.obj.map (homOfLE (le_top : iSup (tupleOpen X U) ≤ ⊤)).op)).mp inferInstance s
  refine ⟨t, fun a => ?_⟩
  have h := hs a
  rw [← ht] at h
  change F.obj.map _ (F.obj.map _ t) = _ at h
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechZero
