import OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification

/-! # Sheaf Section Constant -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionConstant.SheafSectionCoefficientRestriction

noncomputable section

/-! # Actual section coordinates under restriction and coefficient transport -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C D A A' : Type*} [Category C] [Category D] [Category A] [Category A']
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify J A']
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  (R : A ⥤ A') [J.HasSheafCompose R] [J.PreservesSheafification R]
  (a : A) (a' : A') (e : R.obj a ≅ a')

def constantIso : ((F.op ⋙ (Functor.const Dᵒᵖ).obj a) ⋙ R) ≅ (Functor.const Cᵒᵖ).obj a' :=
  constComp Cᵒᵖ a R ≪≫ (Functor.const Cᵒᵖ).mapIso e

def constantTransport :
    (sheafCompose J R).obj ((F.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj a)) ≅
      (constantSheaf J A').obj a' :=
  NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transported J K F R
    ((Functor.const Dᵒᵖ).obj a) ((Functor.const Cᵒᵖ).obj a') (constantIso F R a a' e)

variable (M : Sheaf K A) (N : Sheaf J A')
  (s : (constantSheaf K A).obj a ⟶ M)
  (f : (sheafCompose J R).obj ((F.sheafPushforwardContinuous A J K).obj M) ⟶ N)

theorem homEquiv :
    (sheafificationAdjunction J A').homEquiv ((Functor.const Cᵒᵖ).obj a') N
      ((constantTransport J K F R a a' e).inv ≫
        (sheafCompose J R).map ((F.sheafPushforwardContinuous A J K).map s) ≫ f) =
    (constantIso F R a a' e).inv ≫
      whiskerRight (whiskerLeft F.op ((sheafificationAdjunction K A).homEquiv
        ((Functor.const Dᵒᵖ).obj a) M s)) R ≫ f.hom := by
  let P := (Functor.const Dᵒᵖ).obj a
  let Q := (Functor.const Cᵒᵖ).obj a'
  let c : ((F.op ⋙ P) ⋙ R) ≅ Q := constantIso F R a a' e
  let t : sheafify J Q ⟶ ((F.op ⋙ sheafify K P) ⋙ R) :=
    (constantTransport J K F R a a' e).inv.hom
  let s₀ : sheafify K P ⟶ M.obj := s.hom
  let f₀ : (F.op ⋙ M.obj) ⋙ R ⟶ N.obj := f.hom
  change toSheafify J Q ≫ (t ≫ (whiskerRight (whiskerLeft F.op s₀) R ≫ f₀)) =
    c.inv ≫ whiskerRight (whiskerLeft F.op (toSheafify K P ≫ s₀)) R ≫ f₀
  rw [whiskerLeft_comp, whiskerRight_comp]
  have h : toSheafify J Q ≫ t = c.inv ≫ whiskerRight (whiskerLeft F.op (toSheafify K P)) R :=
    NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transported_generator J K F R P Q c
  rw [← Category.assoc, h]
  simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionConstant.SheafSectionCoefficientRestriction
