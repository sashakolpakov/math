import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Constant Forget -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantForget.ConstantForgetGenerators

noncomputable section

/-! Forgetting coefficients in a constant sheaf preserves its canonical generating maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits

variable {C A B : Type*} [Category* C] [Category* A] [Category* B]
  (J : GrothendieckTopology C) (F : A ⥤ B)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  [J.PreservesSheafification F] [J.HasSheafCompose F]

theorem hom_generator (X : A) :
    whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj X)) F ≫
      ((constantCommuteCompose J F).hom.app X).hom =
        (Functor.constComp Cᵒᵖ X F).hom ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj X)) := by
  rw [constantCommuteCompose_hom_app_hom]
  erw [sheafComposeIso_inv_fac_assoc, ← toSheafify_naturality]

theorem inv_generator (X : A) :
    (Functor.constComp Cᵒᵖ X F).hom ≫ toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj X)) ≫
      ((constantCommuteCompose J F).inv.app X).hom =
        whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj X)) F := by
  erw [← Category.assoc, ← hom_generator, Category.assoc]
  have h := congrArg (fun k => k.hom) ((constantCommuteCompose J F).hom_inv_id_app X)
  change ((constantCommuteCompose J F).hom.app X).hom ≫
    ((constantCommuteCompose J F).inv.app X).hom = 𝟙 _ at h
  erw [h, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantForget.ConstantForgetGenerators
