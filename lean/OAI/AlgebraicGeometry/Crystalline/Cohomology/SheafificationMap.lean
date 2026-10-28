import OAI.NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification

/-! # Sheafification Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationMap.SheafificationMapGenerators

noncomputable section

/-! # Original sheafification comparisons carry actual mapped presheaf generators -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

variable {C D A : Type*} [Category C] [Category D] [Category A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]

theorem generator (P : Dᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A) (f : F.op ⋙ P ⟶ Q) :
    whiskerLeft F.op (toSheafify K P) ≫
      ((NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence.transport J K F P).hom.hom ≫ sheafifyMap J f) =
      f ≫ toSheafify J Q :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ sheafifyMap J f)
      (NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence.transport_hom_generator J K F P)).trans
      (toSheafify_naturality J f).symm)

variable {A' : Type*} [Category A'] [HasWeakSheafify J A']
  (R : A ⥤ A') [J.HasSheafCompose R] [J.PreservesSheafification R]

theorem changed_hom_generator (P : Dᵒᵖ ⥤ A) :
    whiskerRight (whiskerLeft F.op (toSheafify K P)) R ≫
      (NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport J K F R P).hom.hom =
    toSheafify J ((F.op ⋙ P) ⋙ R) := by
  let e := (sheafToPresheaf J A').mapIso
    (NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport J K F R P)
  have h := NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport_generator J K F R P
  exact (congrArg (fun t => t ≫ e.hom) h).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => toSheafify J ((F.op ⋙ P) ⋙ R) ≫ t) e.inv_hom_id).trans (Category.comp_id _)))

theorem changed_generator (P : Dᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A') (f : (F.op ⋙ P) ⋙ R ⟶ Q) :
    whiskerRight (whiskerLeft F.op (toSheafify K P)) R ≫
      ((NumberTheory.PadicHodge.PeriodInvariants.ChangedCoefficientSheafification.transport J K F R P).hom.hom ≫ sheafifyMap J f) =
      f ≫ toSheafify J Q :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ sheafifyMap J f) (changed_hom_generator J K F R P)).trans
      (toSheafify_naturality J f).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationMap.SheafificationMapGenerators
