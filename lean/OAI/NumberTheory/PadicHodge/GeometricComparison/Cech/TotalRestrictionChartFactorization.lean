import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotal

/-! # Total Restriction Chart Factorization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionChartFactorization.CechTotalRestrictionChartFactorization

noncomputable section

/-! The restricted global total augmentation factors through the
original coefficient augmentation at the chosen chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u a b c d e f g h
variable (C : Type u) [SemilatticeInf C] (I : C)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type c} [Category.{d} B] [Preadditive B]
  {E : Type e} [Category.{f} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  {D : Type g} [Category.{h} D] [Preadditive D]
  (S : A ⥤ B) [S.Additive] (R : B ⥤ D) [R.Additive]
  (T : A ⥤ E) [T.Additive] (L : E ⥤ D) [L.Additive]
  (e : S ⋙ R ≅ T ⋙ L) {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (M : CochainComplex A ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)
  (hm : ∀ V : C, IsIso ((CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped T P).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

theorem factorization :
    (R.mapHomologicalComplex (.up ℕ)).map ((S.mapHomologicalComplex (.up ℕ)).map
      (CechCone.Total.CechConeTotal.augmentation U P M η)) ≫ (TotalRestriction.CechTotalRestrictionComparison.iso S R T L e U P).hom =
    (R.mapHomologicalComplex (.up ℕ)).map ((S.mapHomologicalComplex (.up ℕ)).map (η.app (op I))) ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op I))).hom ≫
        (L.mapHomologicalComplex (.up ℕ)).map
          (Semilattice.ChartTotal.SemilatticeChartTotal.map C U I (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped T P) hm) := by
  let Q := CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped T P
  let η' := CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone T P M η
  have hf := Semilattice.ChartTotal.SemilatticeChartTotal.factorization C U I Q hm
    ((T.mapHomologicalComplex (.up ℕ)).obj M) η'
  have hn : (R.mapHomologicalComplex (.up ℕ)).map ((S.mapHomologicalComplex (.up ℕ)).map (η.app (op I))) ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op I))).hom =
    ((NatIso.mapHomologicalComplex e (.up ℕ)).app M).hom ≫
      (L.mapHomologicalComplex (.up ℕ)).map ((T.mapHomologicalComplex (.up ℕ)).map (η.app (op I))) :=
    (NatIso.mapHomologicalComplex e (.up ℕ)).hom.naturality (η.app (op I))
  rw [TotalRestrictionAugmentation.CechTotalRestrictionAugmentation.augmentation]
  change _ ≫ (L.mapHomologicalComplex (.up ℕ)).map (CechCone.Total.CechConeTotal.augmentation U Q
    ((T.mapHomologicalComplex (.up ℕ)).obj M) η') = _
  rw [hf, CategoryTheory.Functor.map_comp]
  dsimp only [η']
  rw [CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app]
  erw [← Category.assoc, ← hn, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionChartFactorization.CechTotalRestrictionChartFactorization
