import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Changed Coefficient Sheafification -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification

noncomputable section

/-!
# Generators for sheafification with a change of coefficients

Exact restriction and a coefficient functor preserving sheafification
carry presheaf generators through their canonical comparison maps. This
characterizes the transports used by semilinear crystalline base twist.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C D A A' : Type*} [Category C] [Category D] [Category A] [Category A']
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify J A']
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
variable (R : A ⥤ A') [J.HasSheafCompose R] [J.PreservesSheafification R]

def transport (P : Dᵒᵖ ⥤ A) :
    (sheafCompose J R).obj ((F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P)) ≅
      (presheafToSheaf J A').obj ((F.op ⋙ P) ⋙ R) :=
  (sheafCompose J R).mapIso (SheafificationCoherence.transport J K F P) ≪≫
    ((sheafComposeNatIso J R (sheafificationAdjunction J A) (sheafificationAdjunction J A')).app
      (F.op ⋙ P)).symm

theorem transport_generator (P : Dᵒᵖ ⥤ A) :
    toSheafify J ((F.op ⋙ P) ⋙ R) ≫ (transport J K F R P).inv.hom =
      whiskerRight (whiskerLeft F.op (toSheafify K P)) R := by
  change toSheafify J ((F.op ⋙ P) ⋙ R) ≫
    ((sheafifyComposeIso J R (F.op ⋙ P)).hom ≫
      whiskerRight (SheafificationCoherence.transport J K F P).inv.hom R) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ whiskerRight (SheafificationCoherence.transport J K F P).inv.hom R)
      (sheafComposeIso_hom_fac J R (F.op ⋙ P))).trans
      ((whiskerRight_comp (toSheafify J (F.op ⋙ P))
        (SheafificationCoherence.transport J K F P).inv.hom R).symm.trans
          (congrArg (fun z => whiskerRight z R)
            (SheafificationCoherence.transport_generator J K F P))))

def transported (P : Dᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A') (e : (F.op ⋙ P) ⋙ R ≅ Q) :
    (sheafCompose J R).obj ((F.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P)) ≅
      (presheafToSheaf J A').obj Q :=
  transport J K F R P ≪≫ (presheafToSheaf J A').mapIso e

theorem transported_generator (P : Dᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A') (e : (F.op ⋙ P) ⋙ R ≅ Q) :
    toSheafify J Q ≫ (transported J K F R P Q e).inv.hom =
      e.inv ≫ whiskerRight (whiskerLeft F.op (toSheafify K P)) R := by
  change toSheafify J Q ≫ (sheafifyMap J e.inv ≫ (transport J K F R P).inv.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (transport J K F R P).inv.hom) (toSheafify_naturality J e.inv).symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => e.inv ≫ z) (transport_generator J K F R P))))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification
