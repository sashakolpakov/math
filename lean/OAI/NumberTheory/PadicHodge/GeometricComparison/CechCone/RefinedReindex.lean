import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindexCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Refined Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.RefinedReindex.CechConeComparisonRefinedReindex

noncomputable section

/-! The original section-cone comparison commutes with a projected
refinement and an additive change of section coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v uD vD w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {E : Type w''} [Category.{z''} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  (F : C ⥤ D) (S : A ⥤ B) [S.Additive] (H : B ⥤ E) [H.Additive]
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ) (M : CochainComplex B ℕ)
  (η : (Functor.const Dᵒᵖ).obj M ⟶ TotalCoefficient.CechConeTotalCoefficient.mapped S P)

def comparison : M ⟶ (S.mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total V P) :=
  Total.CechConeTotal.augmentation V (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso S V P).inv

def mappedCone := Functor.whiskerLeft F.op
  (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone H (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η)

def refined : (H.mapHomologicalComplex (.up ℕ)).obj M ⟶
    ((S ⋙ H).mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total U (F.op ⋙ P)) :=
  Total.CechConeTotal.augmentation U (F.op ⋙ TotalCoefficient.CechConeTotalCoefficient.mapped (S ⋙ H) P)
    ((H.mapHomologicalComplex (.up ℕ)).obj M) (mappedCone F S H P M η) ≫
      (TotalCoefficient.CechConeTotalCoefficient.totalIso (S ⋙ H) U (F.op ⋙ P)).inv

theorem natural : (H.mapHomologicalComplex (.up ℕ)).map (comparison S V P M η) ≫
    ((S ⋙ H).mapHomologicalComplex (.up ℕ)).map (TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r P) =
      refined F S H U P M η := by
  let HH := H.mapHomologicalComplex (.up ℕ)
  let SH := (S ⋙ H).mapHomologicalComplex (.up ℕ)
  let a := Total.CechConeTotal.augmentation V (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η
  let e := TotalCoefficient.CechConeTotalCoefficient.totalIso S V P
  let d := TotalCoefficient.CechConeTotalCoefficient.totalIso H V (TotalCoefficient.CechConeTotalCoefficient.mapped S P)
  let c := TotalCoefficient.CechConeTotalCoefficient.totalIso (S ⋙ H) U (F.op ⋙ P)
  let f := TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r P
  let b := TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r (TotalCoefficient.CechConeTotalCoefficient.mapped (S ⋙ H) P)
  let η' := TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone H (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η
  let a' := Total.CechConeTotal.augmentation U (F.op ⋙ TotalCoefficient.CechConeTotalCoefficient.mapped (S ⋙ H) P) (HH.obj M)
    (Functor.whiskerLeft F.op η')
  let aV := Total.CechConeTotal.augmentation V (TotalCoefficient.CechConeTotalCoefficient.mapped (S ⋙ H) P) (HH.obj M) η'
  have hInv : HH.map e.inv ≫ (TotalCoefficient.CechConeTotalCoefficient.totalIso (S ⋙ H) V P).hom = d.hom :=
    (congrArg (fun q => HH.map e.inv ≫ q) (CoefficientComposition.CechConeCoefficientComposition.total S H V P)).trans
      ((HH.mapIso e).inv_hom_id_assoc d.hom)
  have hRef := TotalRefinedReindexCoefficient.CechConeTotalRefinedReindexCoefficient.total F (S ⋙ H) U V r P
  have hAug : HH.map a ≫ d.hom = aV :=
    TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation H V (TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η
  have hRefAug : aV ≫ b = a' := TotalRefinedReindex.CechConeTotalRefinedReindex.augmentation F U V r
    (TotalCoefficient.CechConeTotalCoefficient.mapped (S ⋙ H) P) (HH.obj M) η'
  apply (cancel_mono c.hom).mp
  change (HH.map (a ≫ e.inv) ≫ SH.map f) ≫ c.hom = (a' ≫ c.inv) ≫ c.hom
  have hStart : (HH.map (a ≫ e.inv) ≫ SH.map f) ≫ c.hom =
      HH.map a ≫ (HH.map e.inv ≫ (SH.map f ≫ c.hom)) :=
    (congrArg (fun q => (q ≫ SH.map f) ≫ c.hom) (HH.map_comp a e.inv)).trans
      ((Category.assoc _ _ _).trans (Category.assoc _ _ _))
  have hSecond := congrArg (fun q => HH.map a ≫ (HH.map e.inv ≫ q)) hRef
  have hThird := congrArg (fun q => HH.map a ≫ q)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ b) hInv))
  have hLast : a' = (a' ≫ c.inv) ≫ c.hom :=
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => a' ≫ q) c.inv_hom_id).trans (Category.comp_id a'))).symm
  exact hStart.trans (hSecond.trans (hThird.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ b) hAug).trans (hRefAug.trans hLast)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.RefinedReindex.CechConeComparisonRefinedReindex
