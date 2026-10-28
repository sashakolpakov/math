import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularScalars
import OAI.Algebra.Homology.Notation

/-! # Canonical Singular Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularNaturality

noncomputable section

/-! # Naturality of the canonical singular-to-hypercohomology comparison -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : Over (Spec ↧ℂ))

set_option backward.isDefEq.respectTransparency false in
/-- Changing from integer degrees to natural degrees respects every actual endomorphism
of the singular-cochain resolution. -/
lemma singularGlobalIntegerHomologyIso_naturality
    (f : AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X) ⟶
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ).map
            (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n).hom =
      (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n).hom ≫ HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n := by
  let Γ := AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let K := AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let e := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  let L := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have h := congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ))
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality Γ K ComplexShape.embeddingUpNat f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  change HomologicalComplex.homologyMap _ (n : ℤ) ≫
      HomologicalComplex.homologyMap e.hom (n : ℤ) ≫
        (L.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom =
    (HomologicalComplex.homologyMap e.hom (n : ℤ) ≫
      (L.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom) ≫ _
  have hL := HomologicalComplex.extendHomologyIso_hom_naturality
    ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map f) ComplexShape.embeddingUpNat
    (j := n) (hj' := rfl)
  rw [← Category.assoc, h, Category.assoc]
  exact (congrArg (fun m => HomologicalComplex.homologyMap e.hom (n : ℤ) ≫ m) hL).trans
    (Category.assoc _ _ _).symm

variable [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical natural-degree global comparison respects all endomorphisms of
the original resolution. -/
lemma singularGlobalToHypercohomologyAddEquiv_naturality
    (f : AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X) ⟶
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ)
    (z : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X)).homology n) :
    CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n
        (HomologicalComplex.homologyMap
          (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n z) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) n
        (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n z) := by
  let e := Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n
  have h : HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫ e.inv =
      e.inv ≫ HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ).map
            (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      singularGlobalIntegerHomologyIso_naturality, Iso.inv_hom_id_assoc]
  change GlobalNaturality.globalSectionsToHypercohomology X _ (n : ℤ)
    (e.inv (HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n z)) = _
  have hz := congrArg (fun g => g z) h
  change e.inv (HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n z) =
    HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ).map
          (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) (n : ℤ) (e.inv z) at hz
  exact (congrArg (GlobalNaturality.globalSectionsToHypercohomology X _ (n : ℤ)) hz).trans
    (GlobalNaturality.globalSectionsToHypercohomology_naturality X
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) n (e.inv z))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularNaturality
