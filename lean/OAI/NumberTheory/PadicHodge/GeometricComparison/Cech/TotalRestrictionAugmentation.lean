import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Total Restriction Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionAugmentation.CechTotalRestrictionAugmentation

noncomputable section

/-! The actual restriction/sheafification total isomorphism preserves
the canonical augmentation and its original source comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a b c d e f g h
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type c} [Category.{d} B] [Preadditive B]
  {E : Type e} [Category.{f} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  {D : Type g} [Category.{h} D] [Preadditive D]
  (S : A ⥤ B) [S.Additive] (R : B ⥤ D) [R.Additive]
  (T : A ⥤ E) [T.Additive] (L : E ⥤ D) [L.Additive]
  (e : S ⋙ R ≅ T ⋙ L) {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (M : CochainComplex A ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

theorem augmentation :
    (R.mapHomologicalComplex (.up ℕ)).map ((S.mapHomologicalComplex (.up ℕ)).map
      (CechCone.Total.CechConeTotal.augmentation U P M η)) ≫ (TotalRestriction.CechTotalRestrictionComparison.iso S R T L e U P).hom =
    ((NatIso.mapHomologicalComplex e (.up ℕ)).app M).hom ≫
      (L.mapHomologicalComplex (.up ℕ)).map
        (CechCone.Total.CechConeTotal.augmentation U (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped T P)
          ((T.mapHomologicalComplex (.up ℕ)).obj M) (CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone T P M η)) := by
  let a := CechCone.Total.CechConeTotal.augmentation U P M η
  let b := (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P).hom
  let m := ((NatIso.mapHomologicalComplex e (.up ℕ)).app M).hom
  have hn : (R.mapHomologicalComplex (.up ℕ)).map ((S.mapHomologicalComplex (.up ℕ)).map a) ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app (CechCone.Total.CechConeTotal.total U P)).hom =
    m ≫ (L.mapHomologicalComplex (.up ℕ)).map ((T.mapHomologicalComplex (.up ℕ)).map a) :=
    (NatIso.mapHomologicalComplex e (.up ℕ)).hom.naturality a
  change _ ≫ (((NatIso.mapHomologicalComplex e (.up ℕ)).app (CechCone.Total.CechConeTotal.total U P)).hom ≫
      (L.mapHomologicalComplex (.up ℕ)).map b) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (L.mapHomologicalComplex (.up ℕ)).map b) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => m ≫ k)
        (((L.mapHomologicalComplex (.up ℕ)).map_comp _ _).symm.trans
          (congrArg (fun k => (L.mapHomologicalComplex (.up ℕ)).map k)
            (CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation T U P M η))))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionAugmentation.CechTotalRestrictionAugmentation
