import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentGradedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowClass

/-! # Component Chow Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentChowClass.BundleCycles

noncomputable section

/-! The actual graph normal bundle over every source component carries
the descended geometric Chow cycle class, and its Chow extension has
the canonical Betti pullback formula in the actual receiving rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

instance graphConeOver_separated : IsSeparated (Graph.Conormal.BundleCycles.graphConeOver f).hom := by
  change IsSeparated (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.Chow.BundleCycles.graphAmbientStructureMap f)
  rw [← Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase]
  infer_instance

instance graphNormalComponentOver_separated : IsSeparated (ComponentCycleClass.BundleCycles.graphNormalComponentOver f C).hom := by
  have h := (ComponentCycleClass.BundleCycles.graphNormalComponentInclusionOver f C).w
  rw [← h]
  exact IsSeparated.stableUnderComposition.comp_mem (ComponentCycleClass.BundleCycles.graphNormalComponentInclusionOver f C).left
    (Graph.Conormal.BundleCycles.graphConeOver f).hom inferInstance inferInstance

local notation "V" => X.componentVariety C
local notation "N" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentOver f C
local notation "q" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentProjectionOver f C
local notation "r" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentGradedClass.BundleCycles.graphNormalComponentFiberRank f C
local notation "h" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentRank.BundleCycles.graphNormalComponent_hasAffineSpaceChartsOfRank f C

local instance e13GraphNormalComponentChowClass_local1 : IsIntegral (V).toOver.left := inferInstanceAs (IsIntegral (V).carrier)
local instance e13GraphNormalComponentChowClass_local2 : Smooth (V).toOver.hom := inferInstanceAs (Smooth (V).structureMap)
local instance e13GraphNormalComponentChowClass_local3 : IsSeparated (V).toOver.hom := inferInstanceAs (IsSeparated (V).structureMap)
local instance e13GraphNormalComponentChowClass_local4 : AlgebraicGeometry.IsNoetherian (V).toOver.left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (V).carrier)
local instance e13GraphNormalComponentChowClass_local5 : IsLocallyNoetherian (V).toOver.left := inferInstanceAs (IsLocallyNoetherian (V).carrier)

def graphNormalComponentChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (V).structureMap d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (N).hom (d + r) :=
  AffineBundle.ChowClass.Cycles.affineBundleOverChowExtension q r h d

theorem graphNormalComponentChowExtension_cycle (d : ℕ)
    (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (X.componentVariety C).structureMap d →₀ ℚ) :
    graphNormalComponentChowExtension f C d (DimensionChow.BundleCycles.dimensionCycleToChowQ (V).structureMap d a) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (N).hom (d + r) (ComponentGradedClass.BundleCycles.graphNormalComponentGradedExtension f C d a) :=
  AffineBundle.ChowClass.Cycles.affineBundleOverChowExtension_cycle q r h d a

theorem graphNormalComponentChowClass (d p : ℕ)
    (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (V).structureMap)
    (a : DimensionChow.BundleCycles.DimensionChowQ (X.componentVariety C).structureMap d) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass N (d + r) p (AffineBundle.OverGrading.Cycles.affineBundleOver_complementDegree q r h d p hd)
      (graphNormalComponentChowExtension f C d a) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) q
      (Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass (V).toOver d p hd a) :=
  AffineBundle.ChowClass.Cycles.schemeDimensionChowCycleClass_affineBundle q r h d p hd a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentChowClass.BundleCycles
