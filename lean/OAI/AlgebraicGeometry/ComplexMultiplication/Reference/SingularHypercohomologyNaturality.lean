import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularGlobalNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.MapExtendComposition
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularComparison

/-! # Singular Hypercohomology Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularHypercohomologyNaturality

noncomputable section

/-! # The original singular global/hypercohomology comparison respects scheme maps -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable {X Y : Over (Spec (.of ℂ))} (R : Type) [Field R]

/-- Actual original singular pullback on integer-indexed global-section complexes. -/
def originalSingularGlobalPullbackInt (f : X ⟶ Y) :
    Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
        (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) ⟶
      Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) :=
  GlobalPullback.originalGlobalSectionsComplexInverseImage f (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) ≫
    ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (SingularInverseImage.originalSingularInverseImagePullback R f)

/-- The actual natural- and integer-indexed global pullbacks retain the original normalization. -/
theorem originalSingularGlobalPullbackInt_extend (f : X ⟶ Y) :
    originalSingularGlobalPullbackInt R f ≫
        (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
          (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
          ComplexShape.embeddingUpNat).hom =
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
        (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
        ComplexShape.embeddingUpNat).hom ≫
          HomologicalComplex.extendMap (SingularGlobalNaturality.originalSingularGlobalPullback R f)
            ComplexShape.embeddingUpNat := by
  have h := MapExtendComposition.mapExtendNaturalComposite (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    (GlobalSheafPullback.originalGlobalSectionsInverseImageNat f)
    (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (SingularInverseImage.originalSingularInverseImagePullbackNat R f) ComplexShape.embeddingUpNat
  exact h.trans (congrArg (fun g ↦
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
      (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
      ComplexShape.embeddingUpNat).hom ≫
        HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)
    (SingularGlobalNaturality.originalSingularGlobalPullback_adjunction R f))

set_option backward.isDefEq.respectTransparency false in
/-- The original integer/natural homology comparison commutes with actual scheme pullback. -/
theorem originalSingularGlobalIntegerHomologyIso_naturality (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (originalSingularGlobalPullbackInt R f) (n : ℤ) ≫
        (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n).hom =
      (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R Y n).hom ≫
        HomologicalComplex.homologyMap (SingularGlobalNaturality.originalSingularGlobalPullback R f) n := by
  let ΓX := AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  let ΓY := AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
  let eX := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso ΓX
    (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ComplexShape.embeddingUpNat
  let eY := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso ΓY
    (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ComplexShape.embeddingUpNat
  let LX := AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  let LY := AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
  have h := congrArg (fun g ↦ HomologicalComplex.homologyMap g (n : ℤ))
    (originalSingularGlobalPullbackInt_extend R f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  change HomologicalComplex.homologyMap _ (n : ℤ) ≫
      HomologicalComplex.homologyMap eX.hom (n : ℤ) ≫
        (LX.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom =
    (HomologicalComplex.homologyMap eY.hom (n : ℤ) ≫
      (LY.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom) ≫ _
  have hL := HomologicalComplex.extendHomologyIso_hom_naturality
    (SingularGlobalNaturality.originalSingularGlobalPullback R f) ComplexShape.embeddingUpNat (j := n) (hj' := rfl)
  rw [← Category.assoc, h, Category.assoc]
  exact (congrArg (fun m ↦ HomologicalComplex.homologyMap eY.hom (n : ℤ) ≫ m) hL).trans
    (Category.assoc _ _ _).symm

/-- Actual integer global pullback commutes with the original canonical hypercohomology map. -/
theorem originalSingularGlobalToHypercohomologyInt_naturality (f : X ⟶ Y) (n : ℤ)
    (z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))
      (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R)).homology n) :
    GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) n
        (HomologicalComplex.homologyMap (originalSingularGlobalPullbackInt R f) n z) =
      SingularConstantNaturality.originalSingularHypercohomologyPullback R f n
        (GlobalNaturality.globalSectionsToHypercohomology Y (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) n z) := by
  let u := GlobalPullback.originalGlobalSectionsComplexInverseImage f (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R)
  let v := ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (SingularInverseImage.originalSingularInverseImagePullback R f)
  have hc := ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp u v n) z
  have hn := GlobalNaturality.globalSectionsToHypercohomology_naturality X
    (SingularInverseImage.originalSingularInverseImagePullback R f) n (HomologicalComplex.homologyMap u n z)
  have hi := GlobalHypercohomologyNaturality.globalSectionsToHypercohomology_inverseImage f
    (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) n z
  exact (congrArg (GlobalNaturality.globalSectionsToHypercohomology X _ n) hc).trans
    (hn.trans (congrArg (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularInverseImage.originalSingularInverseImagePullback R f) n) hi))

variable [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [Foundations.ProjectiveSpaceIs.IsProjective Y.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The unchanged canonical natural-degree singular comparison respects actual scheme maps. -/
theorem originalSingularGlobalToHypercohomology_naturality (f : X ⟶ Y) (n : ℕ)
    (z : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).homology n) :
    CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n
        (HomologicalComplex.homologyMap (SingularGlobalNaturality.originalSingularGlobalPullback R f) n z) =
      SingularConstantNaturality.originalSingularHypercohomologyPullback R f (n : ℤ)
        (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R Y n z) := by
  let eX := Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n
  let eY := Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R Y n
  have h : HomologicalComplex.homologyMap (SingularGlobalNaturality.originalSingularGlobalPullback R f) n ≫ eX.inv =
      eY.inv ≫ HomologicalComplex.homologyMap (originalSingularGlobalPullbackInt R f) (n : ℤ) := by
    apply (cancel_mono eX.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      originalSingularGlobalIntegerHomologyIso_naturality, Iso.inv_hom_id_assoc]
  have hz := ConcreteCategory.congr_hom h z
  change GlobalNaturality.globalSectionsToHypercohomology X _ (n : ℤ)
      (eX.inv (HomologicalComplex.homologyMap (SingularGlobalNaturality.originalSingularGlobalPullback R f) n z)) = _
  exact (congrArg (GlobalNaturality.globalSectionsToHypercohomology X _ (n : ℤ)) hz).trans
    (originalSingularGlobalToHypercohomologyInt_naturality R f (n : ℤ) (eY.inv z))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularHypercohomologyNaturality
