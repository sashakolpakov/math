import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientGlobalUnits
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison

/-! # Rational Coefficient Hypercohomology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientHypercohomology

noncomputable section

/-! # Actual coefficient naturality of the original global and hypercohomology comparisons -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable (R S : Type) [Field R] [Field S] (X : Over (Spec (.of ℂ)))

set_option backward.isDefEq.respectTransparency false in
/-- Natural-to-integer global transport commutes with a map between different coefficient resolutions. -/
theorem singularGlobalIntegerHomologyIso_coefficient_naturality
    (f : AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⟶
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex S (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso S X n).hom =
      (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n).hom ≫ HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n := by
  let Γ := AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  let K := AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  let L := AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex S (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  let eK := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  let eL := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso Γ L ComplexShape.embeddingUpNat
  let KL := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let LL := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
  have h := congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ))
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality Γ K ComplexShape.embeddingUpNat f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  change HomologicalComplex.homologyMap _ (n : ℤ) ≫
      HomologicalComplex.homologyMap eL.hom (n : ℤ) ≫
        (LL.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom =
    (HomologicalComplex.homologyMap eK.hom (n : ℤ) ≫
      (KL.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom) ≫ _
  have hL := HomologicalComplex.extendHomologyIso_hom_naturality
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f) ComplexShape.embeddingUpNat
    (j := n) (hj' := rfl)
  rw [← Category.assoc, h, Category.assoc]
  exact (congrArg (fun m => HomologicalComplex.homologyMap eK.hom (n : ℤ) ≫ m) hL).trans
    (Category.assoc _ _ _).symm

variable [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The original global-to-hypercohomology equivalences retain maps between different coefficients. -/
theorem singularGlobalToHypercohomologyAddEquiv_coefficient_naturality
    (f : AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⟶
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex S (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (n : ℕ)
    (z : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).homology n) :
    CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv S X n
        (HomologicalComplex.homologyMap
          (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n z) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) n
        (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n z) := by
  let eR := Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n
  let eS := Coefficient.SheafComparison.singularGlobalIntegerHomologyIso S X n
  have h : HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫ eS.inv =
      eR.inv ≫ HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) := by
    apply (cancel_mono eS.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      singularGlobalIntegerHomologyIso_coefficient_naturality, Iso.inv_hom_id_assoc]
  change GlobalNaturality.globalSectionsToHypercohomology X _ (n : ℤ)
    (eS.inv (HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n z)) = _
  have hz := ConcreteCategory.congr_hom h z
  change eS.inv (HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n z) =
    HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) (eR.inv z) at hz
  exact (congrArg (GlobalNaturality.globalSectionsToHypercohomology X _ (n : ℤ)) hz).trans
    (GlobalNaturality.globalSectionsToHypercohomology_naturality X
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) n (eR.inv z))

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The original constant resolution comparison retains the actual rational coefficient inclusion. -/
theorem constantHypercohomologySingularAddEquiv_rational_coefficient (n : ℕ)
    (z : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X) n) :
    Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℂ X n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n z) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (RationalCoefficient.originalRationalToComplexSingularSheafIntMap X) n
        (Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℚ X n z) := by
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ) n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n z) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (RationalCoefficient.originalRationalToComplexSingularSheafIntMap X) n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℚ) n z)
  exact (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X)
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ) n z).symm.trans <|
    (congrArg (fun f => ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n z)
      (RationalCoefficient.originalRationalToComplexSingularSheafIntMap_constants X).symm).trans <|
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℚ)
      (RationalCoefficient.originalRationalToComplexSingularSheafIntMap X) n z

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientHypercohomology
