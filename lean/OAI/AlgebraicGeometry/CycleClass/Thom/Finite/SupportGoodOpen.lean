import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper

/-! # Support Good Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportGoodOpen.Constructions

noncomputable section

/-! Finite maps on actual reduced supports have genuine smooth finite-etale
generic opens, with all dimension and properness conditions derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Y.hom]
  (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

/-- Both smoothness conditions refer to the original structure morphisms. -/
theorem exists_smooth_etale_open :
    ∃ U : (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport f Z)).Opens,
      genericPoint (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport f Z)) ∈ U ∧
      IsFinite (Scheme.ProperSupport.Constructions.imageMap f Z ∣_ U) ∧ Etale (Scheme.ProperSupport.Constructions.imageMap f Z ∣_ U) ∧
      Smooth (U.ι ≫ Geometric.SupportFiniteType.supportStructureMap (Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom) ∧
      Smooth (((Scheme.ProperSupport.Constructions.imageMap f Z) ⁻¹ᵁ U).ι ≫ Geometric.SupportFiniteType.supportStructureMap Z X.hom) := by
  let i := Scheme.ProperSupport.Constructions.imageMap f Z
  let g := Geometric.SupportFiniteType.supportStructureMap (Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom
  let : IsFinite i := Scheme.ProperSupport.Constructions.imageMap_finite f Z
  let : IsLocallyNoetherian (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport f Z)) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨U, hU, hfin, het, hsT, hsZ⟩ := ProperImage.SmoothEtaleOpen.Constructions.Construction.exists_generic_smooth_finiteEtale_open i g
    (Scheme.ProperSupport.Constructions.imageMap_genericPoint f Z) (Integral.MapDimension.Constructions.integral_dominant_dimension i
      (Scheme.ProperSupport.Constructions.imageMap_genericPoint f Z) g)
  refine ⟨U, hU, hfin, het, hsT, ?_⟩
  change Smooth (((Scheme.ProperSupport.Constructions.imageMap f Z) ⁻¹ᵁ U).ι ≫
    (Scheme.ProperSupport.Constructions.imageMap f Z ≫ Geometric.SupportFiniteType.supportStructureMap (Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom)) at hsZ
  rwa [Scheme.ProperSupport.Constructions.imageMap_over] at hsZ

omit [LocallyOfFiniteType Y.hom] in
/-- Removing the omitted target support boundary forces the entire
source support above it into the chosen inverse-image open. -/
theorem imageBoundary_preimage (U : (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport f Z)).Opens) :
    (Geometric.GenericPoint.reducedSupportι Z ≫ f.left) ⁻¹' (Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary Y (Scheme.ProperSupport.Constructions.imageSupport f Z) U : Set Y.left) =
      (((Scheme.ProperSupport.Constructions.imageMap f Z) ⁻¹ᵁ U) : Set (Geometric.GenericPoint.reducedSupportScheme Z))ᶜ := by
  rw [← Scheme.ProperSupport.Constructions.imageMap_inclusion]
  change (Scheme.ProperSupport.Constructions.imageMap f Z) ⁻¹' ((Geometric.GenericPoint.reducedSupportι (Scheme.ProperSupport.Constructions.imageSupport f Z)) ⁻¹'
    ((Geometric.GenericPoint.reducedSupportι (Scheme.ProperSupport.Constructions.imageSupport f Z)) '' (U : Set (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport f Z)))ᶜ)) = _
  rw [Set.preimage_image_eq _ (Geometric.GenericPoint.reducedSupportι (Scheme.ProperSupport.Constructions.imageSupport f Z)).isClosedEmbedding.injective]
  rfl

/-- The finite restricted support map is analytically proper even when
the source and target are noncompact. -/
theorem restrictedSupport_isProperMap (U : (Geometric.GenericPoint.reducedSupportScheme (Scheme.ProperSupport.Constructions.imageSupport f Z)).Opens) :
    IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (Scheme.ProperSupport.Constructions.imageOverMap f Z) U)) := by
  let : IsFinite (Scheme.ProperSupport.Constructions.imageOverMap f Z).left := Scheme.ProperSupport.Constructions.imageMap_finite f Z
  let : IsFinite (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (Scheme.ProperSupport.Constructions.imageOverMap f Z) U).left := inferInstanceAs
    (IsFinite ((Scheme.ProperSupport.Constructions.imageOverMap f Z).left ∣_ U))
  let : LocallyOfFiniteType (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (Scheme.RegularSupport.Constructions.supportOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z)) U).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Geometric.SupportFiniteType.supportStructureMap (Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom))
  exact Integral.SchemeProper.Constructions.isProperMap_integral (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (Scheme.ProperSupport.Constructions.imageOverMap f Z) U)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportGoodOpen.Constructions
