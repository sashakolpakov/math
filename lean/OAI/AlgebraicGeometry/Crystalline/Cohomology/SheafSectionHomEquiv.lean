import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

/-! # Sheaf Section Hom Equiv -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionHomEquiv.SheafSectionRestriction

noncomputable section

/-! # Original constant-sheaf section coordinates under exact restriction -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C D A : Type*} [Category C] [Category D] [Category A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  (a : A) (M : Sheaf K A) (N : Sheaf J A)
  (s : (constantSheaf K A).obj a ⟶ M)
  (f : (F.sheafPushforwardContinuous A J K).obj M ⟶ N)

theorem homEquiv :
    (sheafificationAdjunction J A).homEquiv ((Functor.const Cᵒᵖ).obj a) N
      ((NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence.transport J K F a).inv ≫
        (F.sheafPushforwardContinuous A J K).map s ≫ f) =
    whiskerLeft F.op ((sheafificationAdjunction K A).homEquiv
      ((Functor.const Dᵒᵖ).obj a) M s) ≫ f.hom := by
  change NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence.constantGenerator J a ≫
      ((NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence.transport J K F a).inv.hom ≫
        (whiskerLeft F.op s.hom ≫ f.hom)) =
    whiskerLeft F.op (NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence.constantGenerator K a ≫ s.hom) ≫ f.hom
  rw [whiskerLeft_comp]
  simp only [← Category.assoc]
  rw [NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence.transport_generator]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionHomEquiv.SheafSectionRestriction
