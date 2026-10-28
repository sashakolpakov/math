import OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification

/-! # Changed Coefficient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ChangedCoefficient.ChangedCoefficientSheafificationNaturality

noncomputable section

/-! # Naturality of the original sheafification comparison with coefficient change -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify J B]
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  (R : A ⥤ B) [J.HasSheafCompose R] [J.PreservesSheafification R]

def iso : presheafToSheaf K A ⋙ F.sheafPushforwardContinuous A J K ⋙ sheafCompose J R ≅
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙
      (Functor.whiskeringRight Cᵒᵖ A B).obj R ⋙ presheafToSheaf J B :=
  isoWhiskerRight (F.pushforwardContinuousSheafificationCompatibility A J K).symm
      (sheafCompose J R) ≪≫
    isoWhiskerLeft ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op)
      (sheafComposeNatIso J R (sheafificationAdjunction J A) (sheafificationAdjunction J B)).symm

theorem component (P : Dᵒᵖ ⥤ A) :
    (iso J K F R).app P =
      NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport J K F R P := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ChangedCoefficient.ChangedCoefficientSheafificationNaturality
