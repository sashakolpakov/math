import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalAdjunction
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularInverseImage
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalHypercohomologyNaturality
import OAI.AlgebraicTopology.Singular.GlobalRestriction

/-! # Singular Global Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularGlobalNaturality

noncomputable section

/-! # Genuine global pullback and the original singular sheafification unit

All maps here are the original singular cochain maps evaluated on the top
open. Actual inverse image yields the same global pullback by adjunction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable {X Y : Over (Spec (.of ℂ))} (R : Type) [CommRing R]

/-- Actual pullback of original raw singular cochains on the top open. -/
def originalRawSingularGlobalPullback (f : X ⟶ Y) :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ⟶
      AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  AlgebraicTopology.Singular.GlobalRestriction.globalRawSingularRestriction R (DeRhamPresheafPullback.originalAnalyticSchemeMap f)

/-- Actual pullback of original singular sheaf global sections. -/
def originalSingularGlobalPullback (f : X ⟶ Y) :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ⟶
      AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  GlobalAdjunction.originalPushforwardGlobalComplexMap f (ComplexShape.up ℕ) _ _
    (AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheafComplex R (DeRhamPresheafPullback.originalAnalyticSchemeMap f))

/-- Genuine inverse image followed by actual singular pullback is original global pullback. -/
theorem originalSingularGlobalPullback_adjunction (f : X ⟶ Y) :
    (NatTrans.mapHomologicalComplex (GlobalSheafPullback.originalGlobalSectionsInverseImageNat f)
        (ComplexShape.up ℕ)).app
          (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ≫
      ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SingularInverseImage.originalSingularInverseImagePullbackNat R f) =
    originalSingularGlobalPullback R f :=
  GlobalAdjunction.originalGlobalComplexInverseImage_adjunction f _ _ _ _

/-- The original double-plus comparison on the preimage top open is the original unit. -/
theorem originalRawPushforwardToSingularSheaf_eq (f : X ⟶ Y) :
    AlgebraicTopology.Singular.GlobalRestriction.globalRawPushforwardToSingularSheaf R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) =
      AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  rw [AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

/-- Original raw pullback and genuine global pullback commute with the original unit. -/
theorem originalRawSingularGlobalPullback_sheafification (f : X ⟶ Y) :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ≫
        originalSingularGlobalPullback R f =
      originalRawSingularGlobalPullback R f ≫
        AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  have h := AlgebraicTopology.Singular.GlobalRestriction.globalSingularSheafRestriction_naturality R (DeRhamPresheafPullback.originalAnalyticSchemeMap f)
  rw [originalRawPushforwardToSingularSheaf_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularGlobalNaturality
