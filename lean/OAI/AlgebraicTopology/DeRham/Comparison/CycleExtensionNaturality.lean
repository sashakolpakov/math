import OAI.AlgebraicGeometry.CycleClass.Geometric.Extension
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality

/-! # Cycle Extension Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CycleExtensionNaturality.DimensionCycleSupport

noncomputable section

/-!
Naturality of the actual extension from a cycle's regular-locus pair.

The maps below are induced by an actual continuous ambient map preserving
the two indicated complements. The extension square follows from the
proved naturality of the inverse of relative-triple restriction. No class
or comparison map is supplied as additional data.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
variable {R : Type} [Ring R]

/-- An ambient map of support complements restricts to a map of the actual
regular-locus complements, after removing the singular boundaries. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPair_mapsTo (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (T : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport W q)
    (f : TopCat.of V.analyticSpace ⟶ TopCat.of W.analyticSpace)
    (hBoundary : Set.MapsTo f Z.analyticSingularBoundaryᶜ T.analyticSingularBoundaryᶜ)
    (hSupport : Set.MapsTo f (Set.range Z.analyticInclusion)ᶜ
      (Set.range T.analyticInclusion)ᶜ) :
    Set.MapsTo (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f hBoundary)
      (Set.range Z.regularComplementInclusion)ᶜ
      (Set.range T.regularComplementInclusion)ᶜ := by
  intro x hx
  apply (T.mem_regularThomComplement_iff _).mpr
  exact hSupport ((Z.mem_regularThomComplement_iff x).mp hx)

/-- Pullback on the genuine regular-locus relative cohomology groups. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPairCohomologyPullback (M : ModuleCat.{0} R)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (T : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport W q)
    (f : TopCat.of V.analyticSpace ⟶ TopCat.of W.analyticSpace)
    (hBoundary : Set.MapsTo f Z.analyticSingularBoundaryᶜ T.analyticSingularBoundaryᶜ)
    (hSupport : Set.MapsTo f (Set.range Z.analyticInclusion)ᶜ
      (Set.range T.analyticInclusion)ᶜ) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of T.regularAmbientSpace)
        (Set.range T.regularComplementInclusion)ᶜ n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f hBoundary)
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPair_mapsTo Z T f hBoundary hSupport) n

/-- The literal identification of each regular pair with its relative-triple
pair commutes with actual pullback of pairs. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_naturality (M : ModuleCat.{0} R)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (T : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport W q)
    (f : TopCat.of V.analyticSpace ⟶ TopCat.of W.analyticSpace)
    (hBoundary : Set.MapsTo f Z.analyticSingularBoundaryᶜ T.analyticSingularBoundaryᶜ)
    (hSupport : Set.MapsTo f (Set.range Z.analyticInclusion)ᶜ
      (Set.range T.analyticInclusion)ᶜ) (n : ℕ) :
    (T.regularThomCohomologyIso M n).hom ≫
        Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f hBoundary)
          (AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeTripleSubspace_mapsTo f hBoundary hSupport) n =
      AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPairCohomologyPullback M Z T f hBoundary hSupport n ≫
        (Z.regularThomCohomologyIso M n).hom := by
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_hom, AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_hom]
  unfold AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPairCohomologyPullback
  rw [Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

/-- Canonical extension from the actual regular pair commutes with a map
of the ambient support and singular-boundary pairs. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_naturality (M : ModuleCat.{0} R)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (T : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport W q)
    (f : TopCat.of V.analyticSpace ⟶ TopCat.of W.analyticSpace)
    (hBoundary : Set.MapsTo f Z.analyticSingularBoundaryᶜ T.analyticSingularBoundaryᶜ)
    (hSupport : Set.MapsTo f (Set.range Z.analyticInclusion)ᶜ
      (Set.range T.analyticInclusion)ᶜ) (n : ℕ)
    (hZ₀ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (hZ₁ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1)))
    (hT₀ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of W.analyticSpace)
      T.analyticSingularBoundaryᶜ n))
    (hT₁ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of W.analyticSpace)
      T.analyticSingularBoundaryᶜ (n + 1))) :
    (T.regularToSupportCohomologyIso M n hT₀ hT₁).hom ≫
        Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hSupport n =
      AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPairCohomologyPullback M Z T f hBoundary hSupport n ≫
        (Z.regularToSupportCohomologyIso M n hZ₀ hZ₁).hom := by
  simp only [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_hom, Category.assoc]
  rw [AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyTripleExtension_naturality M f
    Z.analyticSupportComplement_subset_regularAmbient
    T.analyticSupportComplement_subset_regularAmbient hBoundary hSupport n hZ₀ hZ₁ hT₀ hT₁]
  rw [← Category.assoc, AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_naturality, Category.assoc]

/-- Extending from the regular pair and forgetting support is likewise
natural for the actual ambient continuous map. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToAbsoluteCohomology_naturality (M : ModuleCat.{0} R)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (T : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport W q)
    (f : TopCat.of V.analyticSpace ⟶ TopCat.of W.analyticSpace)
    (hBoundary : Set.MapsTo f Z.analyticSingularBoundaryᶜ T.analyticSingularBoundaryᶜ)
    (hSupport : Set.MapsTo f (Set.range Z.analyticInclusion)ᶜ
      (Set.range T.analyticInclusion)ᶜ) (n : ℕ)
    (hZ₀ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (hZ₁ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1)))
    (hT₀ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of W.analyticSpace)
      T.analyticSingularBoundaryᶜ n))
    (hT₁ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of W.analyticSpace)
      T.analyticSingularBoundaryᶜ (n + 1))) :
    T.regularToAbsoluteCohomology M n hT₀ hT₁ ≫ Cohomology.Singular.Functor.singularCohomologyPullback M f n =
      AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPairCohomologyPullback M Z T f hBoundary hSupport n ≫
        Z.regularToAbsoluteCohomology M n hZ₀ hZ₁ := by
  unfold AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToAbsoluteCohomology
  rw [Category.assoc, ← AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality M f hSupport n,
    ← Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_naturality M Z T f hBoundary hSupport n
      hZ₀ hZ₁ hT₀ hT₁,
    Category.assoc]

end

end OAI.AlgebraicTopology.DeRham.Comparison.CycleExtensionNaturality.DimensionCycleSupport
