import OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Constant Coefficient Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantCoefficientCoherence

noncomputable section

/-!
# Constant generators under a change of coefficients

The canonical comparison for constant sheaves is compatible with their
presheaf generators. The formula retains the canonical constant-functor
isomorphism, so it applies without identifying distinct functor expressions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C A B : Type*} [Category C] [Category A] [Category B]
variable (J : GrothendieckTopology C) [HasWeakSheafify J A] [HasWeakSheafify J B]
variable (R : A ⥤ B) [J.HasSheafCompose R] [J.PreservesSheafification R]

theorem generator (a : A) :
    toSheafify J ((Functor.const Cᵒᵖ).obj (R.obj a)) ≫ ((constantCommuteCompose J R).app a).inv.hom =
      (constComp Cᵒᵖ a R).inv ≫ whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj a)) R := by
  change toSheafify J ((Functor.const Cᵒᵖ).obj (R.obj a)) ≫
    (sheafifyMap J (constComp Cᵒᵖ a R).inv ≫
      (sheafifyComposeIso J R ((Functor.const Cᵒᵖ).obj a)).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (sheafifyComposeIso J R ((Functor.const Cᵒᵖ).obj a)).hom)
      (toSheafify_naturality J (constComp Cᵒᵖ a R).inv).symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (constComp Cᵒᵖ a R).inv ≫ z)
          (sheafComposeIso_hom_fac J R ((Functor.const Cᵒᵖ).obj a)))))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantCoefficientCoherence
