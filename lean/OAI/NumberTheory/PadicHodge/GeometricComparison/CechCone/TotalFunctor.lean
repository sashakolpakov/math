import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality

/-! # Total Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor

noncomputable section

/-! The original Čech total is functorial in complex-valued coefficients,
and its canonical augmentation is natural at the cochain-map level. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C)

local instance hasTotal (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def functor : (Cᵒᵖ ⥤ CochainComplex A ℕ) ⥤ CochainComplex A ℕ :=
  IntegralComparison.NonemptyCechNerve.complexFunctor U ⋙ HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)

omit [HasCoproducts.{0} A] in
theorem obj_eq (P : Cᵒᵖ ⥤ CochainComplex A ℕ) : (functor U).obj P = Total.CechConeTotal.total U P := rfl

variable {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (M : CochainComplex A ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P) (α : P ⟶ Q)

omit [HasCoproducts.{0} A] in
theorem zeroMap : Total.CechConeTotal.zeroMap U P M η ≫ ((IntegralComparison.NonemptyCechNerve.complexFunctor U).map α).f 0 =
    Total.CechConeTotal.zeroMap U Q M (η ≫ α) := by
  have h := congrArg (fun f => f.f 0) (NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality.coefficients U η α)
  rw [HomologicalComplex.comp_f, NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero,
    NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero] at h
  exact h

omit [HasCoproducts.{0} A] in
theorem augmentation : Total.CechConeTotal.augmentation U P M η ≫ (functor U).map α =
    Total.CechConeTotal.augmentation U Q M (η ≫ α) := by
  ext q : 1
  let K := Total.CechConeTotal.bicomplex U P
  let L := Total.CechConeTotal.bicomplex U Q
  let a := (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map
    ((IntegralComparison.NonemptyCechNerve.complexFunctor U).map α)
  have hq := congrArg (fun f => f.f q) (zeroMap U M η α)
  change Total.CechConeTotal.component U P M η q ≫ (a.f q).f 0 =
    Total.CechConeTotal.component U Q M (η ≫ α) q at hq
  change (Total.CechConeTotal.component U P M η q ≫ K.ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map a (.up ℕ)).f q =
    Total.CechConeTotal.component U Q M (η ≫ α) q ≫ L.ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Total.CechConeTotal.component U P M η q ≫ k)
      (HomologicalComplex₂.ιTotal_map K L a (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ L.ιTotal (.up ℕ) q 0 q rfl) hq)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor
