import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularGlobalNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularDualMap

/-! # Singular Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularNaturality

noncomputable section

/-! # Actual raw singular pullback is ordinary singular pullback

The original top-open comparison intertwines the actual chain maps, their
dual cochain maps, and the induced original singular cohomology maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R]

/-- The actual preimage top-open chain map is the ordinary singular chain map. -/
theorem preimageTopChainMap_naturality {U V : TopCat.{0}} (j : U ⟶ V) :
    OAI.AlgebraicTopology.Singular.SheafCochainRestriction.preimageOpenChainMap R j ⊤ ≫ (OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R V).hom =
      (OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R U).hom ≫ OAI.AlgebraicTopology.Singular.CohomologyTo.singularChainComplexMap R j := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)
  change F.map (OAI.AlgebraicTopology.Singular.SheafCochainRestriction.preimageOpenToOpen j ⊤) ≫ F.map (TopologicalSpace.Opens.inclusionTopIso V).hom =
    F.map (TopologicalSpace.Opens.inclusionTopIso U).hom ≫ F.map j
  rw [← F.map_comp, ← F.map_comp]
  rfl

variable {X Y : Over (Spec (.of ℂ))}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged raw cochain comparison commutes with actual scheme-point pullback. -/
theorem originalRawSingularGlobalPullback_cochainIso (f : X ⟶ Y) :
    SingularGlobalNaturality.originalRawSingularGlobalPullback R f ≫
        (SingularDualMap.rawSingularCochainIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).hom =
      (SingularDualMap.rawSingularCochainIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (OAI.AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f)) := by
  have hi : (OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).inv ≫
      OAI.AlgebraicTopology.Singular.SheafCochainRestriction.preimageOpenChainMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) ⊤ =
    OAI.AlgebraicTopology.Singular.CohomologyTo.singularChainComplexMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) ≫
      (OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).inv := by
    apply (cancel_mono (OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).hom).mp
    rw [Category.assoc, preimageTopChainMap_naturality, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  apply AddCommGrpCat.hom_ext
  ext φ
  change OAI.AlgebraicTopology.Singular.SheafCochain.OpenCochains R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) (.op ⊤) n at φ
  apply LinearMap.ext
  intro c
  change φ (((OAI.AlgebraicTopology.Singular.SheafCochainRestriction.preimageOpenChainMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) ⊤).f n).hom
      (((OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).inv.f n).hom c)) =
    φ (((OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).inv.f n).hom
      (((OAI.AlgebraicTopology.Singular.CohomologyTo.singularChainComplexMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).f n).hom c))
  exact congrArg φ (congrArg (fun q ↦ (q.f n).hom c) hi)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged raw homology comparison intertwines the actual original pullbacks. -/
theorem originalRawSingularGlobalPullback_homologyIso (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (SingularGlobalNaturality.originalRawSingularGlobalPullback R f) n ≫
        (Coefficient.SheafComparison.rawSingularHomologyIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n).hom =
      (Coefficient.SheafComparison.rawSingularHomologyIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) n).hom ≫
        (forget₂ (ModuleCat R) AddCommGrpCat).map
          (HomologicalComplex.homologyMap
            (OAI.AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R (DeRhamPresheafPullback.originalAnalyticSchemeMap f)) n) := by
  change HomologicalComplex.homologyMap (SingularGlobalNaturality.originalRawSingularGlobalPullback R f) n ≫
      HomologicalComplex.homologyMap (SingularDualMap.rawSingularCochainIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).hom n
        ≫ _ =
    (HomologicalComplex.homologyMap (SingularDualMap.rawSingularCochainIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).hom n
      ≫ _) ≫ _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    originalRawSingularGlobalPullback_cochainIso, HomologicalComplex.homologyMap_comp,
    Category.assoc, SingularDualMap.forgottenModuleComplex_homology_naturality]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularNaturality
