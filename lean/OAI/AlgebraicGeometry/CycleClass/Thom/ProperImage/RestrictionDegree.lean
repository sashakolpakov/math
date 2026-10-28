import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ResidueDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SmoothEtaleOpen

/-! # Restriction Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

instance openSchemeOver_isIntegral (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
    (U : X.left.Opens) [Nonempty U] : IsIntegral (AnalyticRestriction.Constructions.Construction.openSchemeOver X U).left :=
  inferInstanceAs (IsIntegral U.toScheme)

/-- A dominant map remains dominant after restricting to a nonempty
target open and its nonempty inverse image. -/
theorem restrictedSchemeMap_genericPoint
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (hη : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) [Nonempty U] [Nonempty (f.left ⁻¹ᵁ U)] :
    (AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U).left (genericPoint (AnalyticRestriction.Constructions.Construction.openSchemeOver X (f.left ⁻¹ᵁ U)).left) =
      genericPoint (AnalyticRestriction.Constructions.Construction.openSchemeOver Y U).left := by
  apply U.ι.isOpenEmbedding.injective
  change ((f.left ∣_ U) ≫ U.ι) (genericPoint (f.left ⁻¹ᵁ U).toScheme) =
    U.ι (genericPoint U.toScheme)
  rw [morphismRestrict_ι]
  change f.left ((f.left ⁻¹ᵁ U).ι (genericPoint (f.left ⁻¹ᵁ U).toScheme)) = _
  rw [genericPoint_eq_of_isOpenImmersion (f.left ⁻¹ᵁ U).ι,
    genericPoint_eq_of_isOpenImmersion U.ι, hη]

/-- Restricting to nonempty opens leaves the generic residue degree unchanged. -/
theorem restrictedSchemeMap_residueDegree
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (U : Y.left.Opens) [Nonempty (f.left ⁻¹ᵁ U)] :
    (AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U).left.residueDegree
      (genericPoint (AnalyticRestriction.Constructions.Construction.openSchemeOver X (f.left ⁻¹ᵁ U)).left) =
    f.left.residueDegree (genericPoint X.left) := by
  have h := congrArg
    (fun k : (f.left ⁻¹ᵁ U).toScheme ⟶ Y.left =>
      k.residueDegree (genericPoint (f.left ⁻¹ᵁ U).toScheme)) (morphismRestrict_ι f.left U)
  rw [ResidueDegree.Constructions.Construction.residueDegree_post_immersion, ResidueDegree.Constructions.Construction.residueDegree_pre_immersion,
    genericPoint_eq_of_isOpenImmersion (f.left ⁻¹ᵁ U).ι] at h
  exact h

/-- Smoothness of an open restriction puts the entire open inside
the genuine smooth locus of the original morphism. -/
theorem open_subset_smoothLocus {X S : Scheme} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (U : X.Opens) [Smooth (U.ι ≫ f)] :
    U ≤ f.smoothLocus := by
  intro x hx
  have h : (⟨x, hx⟩ : U) ∈ (U.ι ≫ f).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at h

/-- Actual fibers on a finite etale open have the original map's generic degree. -/
theorem restrictedSchemeMap_fiber_card
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (hη : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) [Nonempty U] [Nonempty (f.left ⁻¹ᵁ U)]
    [IsFinite (f.left ∣_ U)] [Etale (f.left ∣_ U)]
    (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AnalyticRestriction.Constructions.Construction.openSchemeOver Y U)) :
    Nat.card {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AnalyticRestriction.Constructions.Construction.openSchemeOver X (f.left ⁻¹ᵁ U)) //
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U) x = y} =
    f.left.residueDegree (genericPoint X.left) := by
  let : IsFinite (AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U).left := inferInstanceAs (IsFinite (f.left ∣_ U))
  let : Etale (AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U).left := inferInstanceAs (Etale (f.left ∣_ U))
  exact (IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree (AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U)
    (restrictedSchemeMap_genericPoint f hη U) y).trans
    (restrictedSchemeMap_residueDegree f U)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction
