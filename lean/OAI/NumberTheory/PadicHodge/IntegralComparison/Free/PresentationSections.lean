import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Presentation Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSections

noncomputable section

/-! Sections of free presentation presheaves are actual families of sections on the presenting objects. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] {ι : Type v} (F : ι → C)
  (R : Type (max u v)) [CommRing R]

abbrev presheaf : Cᵒᵖ ⥤ ModuleCat.{max u v} R :=
  CoveringPresentationPresheaf.presentations F ⋙ ModuleCat.free R

def lift (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (s : ∀ i, H.obj (op (F i))) :
    presheaf F R ⟶ H where
  app U := ModuleCat.freeDesc (↾fun x => H.map x.down.2.op (s x.down.1))
  naturality U V α := by
    apply ModuleCat.free_hom_ext
    intro x
    change ModuleCat.freeDesc _ ((ModuleCat.free R).map
      ((CoveringPresentationPresheaf.presentations F).map α) (ModuleCat.freeMk x)) = _
    rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply]
    change H.map (α.unop ≫ x.down.2).op (s x.down.1) =
      H.map α (ModuleCat.freeDesc _ (ModuleCat.freeMk x))
    rw [ModuleCat.freeDesc_apply, op_comp, H.map_comp]
    rfl

def evaluate (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (a : presheaf F R ⟶ H) (i : ι) :
    H.obj (op (F i)) :=
  a.app (op (F i)) (ModuleCat.freeMk ⟨⟨i, 𝟙 (F i)⟩⟩)

theorem section_lift (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (s : ∀ i, H.obj (op (F i))) (i : ι) :
    evaluate F R H (lift F R H s) i = s i := by
  change ModuleCat.freeDesc (↾fun x : ULift.{u} (Σ j, F i ⟶ F j) =>
    H.map x.down.2.op (s x.down.1)) (ModuleCat.freeMk ⟨⟨i, 𝟙 (F i)⟩⟩) = s i
  rw [ModuleCat.freeDesc_apply]
  change H.map (𝟙 (op (F i))) (s i) = s i
  rw [H.map_id]
  rfl

theorem lift_section (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (a : presheaf F R ⟶ H) :
    lift F R H (evaluate F R H a) = a := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  intro x
  change ULift.{u} (Σ i, U.unop ⟶ F i) at x
  have h := congrArg (fun b => b (ModuleCat.freeMk ⟨⟨x.down.1, 𝟙 (F x.down.1)⟩⟩))
    (a.naturality x.down.2.op)
  refine (ModuleCat.freeDesc_apply (↾fun y : ULift.{u} (Σ i, U.unop ⟶ F i) =>
    H.map y.down.2.op (evaluate F R H a y.down.1)) x).trans ?_
  have hx : (CoveringPresentationPresheaf.presentations F).map x.down.2.op
      ⟨⟨x.down.1, 𝟙 (F x.down.1)⟩⟩ = x := by
    apply ULift.ext
    exact Sigma.ext rfl (heq_of_eq (Category.comp_id _))
  have hm := (ModuleCat.free_map_apply (R := R)
    ((CoveringPresentationPresheaf.presentations F).map x.down.2.op)
      ⟨⟨x.down.1, 𝟙 (F x.down.1)⟩⟩).trans (congrArg ModuleCat.freeMk hx)
  exact ((congrArg (a.app U) hm).symm.trans h).symm

def homEquiv (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) :
    (presheaf F R ⟶ H) ≃+ (∀ i, H.obj (op (F i))) where
  toFun := evaluate F R H
  invFun := lift F R H
  left_inv := lift_section F R H
  right_inv s := funext (section_lift F R H s)
  map_add' _ _ := rfl

theorem homEquiv_natural {H K : Cᵒᵖ ⥤ ModuleCat.{max u v} R} (g : H ⟶ K)
    (a : presheaf F R ⟶ H) (i : ι) :
    homEquiv F R K (a ≫ g) i = g.app (op (F i)) (homEquiv F R H a i) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSections
