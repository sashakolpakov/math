import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficientAugmentation

/-! # Total Augmentation Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality

noncomputable section

/-! The actual finite Čech total coefficient isomorphism preserves the
canonical total augmentation, including the original total differential. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z w' z' t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{t} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{t} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type t} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

local instance finiteBiproducts : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

omit [HasProducts.{t} B] [Finite ι] in
theorem map_inclusion (q r n : ℕ) (h : q + r = n) :
    F.map ((Total.CechConeTotal.bicomplex U P).ιTotal (.up ℕ) q r n h) ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U P)).inv.f n =
      (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (Total.CechConeTotal.bicomplex U P)).ιTotal (.up ℕ) q r n h := by
  let e := (HomologicalComplex.eval B (.up ℕ) n).mapIso
    (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F (Total.CechConeTotal.bicomplex U P))
  exact e.comp_inv_eq.mpr (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent F
    (Total.CechConeTotal.bicomplex U P) q r n h).symm

variable (M : CochainComplex A ℕ) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

theorem augmentation :
    (F.mapHomologicalComplex (.up ℕ)).map (Total.CechConeTotal.augmentation U P M η) ≫
      (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom =
    Total.CechConeTotal.augmentation U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)
      ((F.mapHomologicalComplex (.up ℕ)).obj M) (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P M η) := by
  ext q : 1
  let K := Total.CechConeTotal.bicomplex U P
  let KF := AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K
  let L := Total.CechConeTotal.bicomplex U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)
  let a := (TotalCoefficient.CechConeTotalCoefficient.bicomplexIso F U P).hom
  let e := (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F K).inv.f q
  let b := (HomologicalComplex₂.total.map a (.up ℕ)).f q
  have hc : F.map (K.ιTotal (.up ℕ) q 0 q rfl) ≫ (e ≫ b) =
      (a.f q).f 0 ≫ L.ιTotal (.up ℕ) q 0 q rfl :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ b) (map_inclusion F U P q 0 q rfl)).trans
        (HomologicalComplex₂.ιTotal_map KF L a (.up ℕ) q 0 q rfl))
  have hq : F.map (Total.CechConeTotal.component U P M η q) ≫ (a.f q).f 0 =
      Total.CechConeTotal.component U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)
        ((F.mapHomologicalComplex (.up ℕ)).obj M)
        (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P M η) q :=
    congrArg (fun α => α.f q) (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.zeroMap F U P M η)
  change F.map (Total.CechConeTotal.component U P M η q ≫ K.ιTotal (.up ℕ) q 0 q rfl) ≫ (e ≫ b) =
    Total.CechConeTotal.component U (TotalCoefficient.CechConeTotalCoefficient.mapped F P)
      ((F.mapHomologicalComplex (.up ℕ)).obj M)
      (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P M η) q ≫ L.ιTotal (.up ℕ) q 0 q rfl
  exact (congrArg (fun k => k ≫ (e ≫ b)) (F.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map (Total.CechConeTotal.component U P M η q) ≫ k) hc).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ L.ιTotal (.up ℕ) q 0 q rfl) hq))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality
