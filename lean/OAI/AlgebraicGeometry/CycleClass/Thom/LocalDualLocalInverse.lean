import OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.OpenFundamental

/-! # Local Dual Local Inverse -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.CanonicalNaturality

/-! Canonical rational point classes are preserved by injective analytic local diffeomorphisms. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.OpenFundamental.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem injectivePunctureMapsTo {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Function.Injective f) (x : X) :
    Set.MapsTo f ({x}ᶜ) ({f x}ᶜ) := fun _ hy h => hy (hf h)

theorem canonicalLocalDual_pullback (d : ℕ) {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N] [T2Space M] [T2Space N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N]
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω f) (x : M) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (injectivePunctureMapsTo f hf x)
      (2 * d) (CanonicalLocalDual.Constructions.canonicalLocalDual d (f x)) = CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  apply CanonicalLocalDual.Constructions.canonicalLocalDual_unique
  rw [AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality]
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of N) ({f x}ᶜ) (2 * d)
    (CanonicalLocalDual.Constructions.canonicalLocalDual d (f x))
    (Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d) (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x)) = 1
  rw [ProperImage.OpenFundamental.Constructions.Construction.complexCanonicalLocalClass_injective_localDiffeomorph d f hf hl x,
    CanonicalLocalDual.Constructions.canonicalLocalDual_integralEvaluation]

theorem canonicalLocalDual_pullback_to (d : ℕ) {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N] [T2Space M] [T2Space N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N]
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω f)
    (x : M) (y : N) (hxy : f x = y) (hp : Set.MapsTo f ({x}ᶜ) ({y}ᶜ)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hp (2 * d)
      (CanonicalLocalDual.Constructions.canonicalLocalDual d y) = CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  subst y
  exact canonicalLocalDual_pullback d f hf hl x

end AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.CanonicalNaturality

namespace AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.Canonical

/-! A local analytic inverse at the sole supported preimage suffices for point-class pullback. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.OpenFundamental.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N]
  [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N]

theorem localClass_map (f : TopCat.of M ⟶ TopCat.of N) (x : M) (y : N) (hxy : f x = y)
    (hp : Set.MapsTo f ({x}ᶜ) ({y}ᶜ))
    (e : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N ω)
    (hx : x ∈ e.source) (he : Set.EqOn f e e.source) :
    Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hp (2 * d) (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) =
      Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  let U := ProperImage.LocalOrientation.Constructions.Construction.analyticPartialSource e
  let x' : U := ⟨x, hx⟩
  let i : TopCat.of U ⟶ TopCat.of M := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)
  have hi : Set.MapsTo i ({x'}ᶜ) ({x}ᶜ) := fun _ hz h => hz (Subtype.ext h)
  have hfe : i ≫ f = ProperImage.LocalOrientation.Constructions.Construction.analyticPartialSourceMap d e := by
    ext z
    exact he z.property
  have hey : e x = y := (he hx).symm.trans hxy
  have hm : Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d) ≫
      Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hp (2 * d) =
    Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMapTo (ProperImage.LocalOrientation.Constructions.Construction.analyticPartialSourceMap d e)
      (ProperImage.LocalOrientation.Constructions.Construction.analyticPartialSourceMap_injective d e) x' y hey (2 * d) :=
    (Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp i f hi hp (2 * d)).trans
      (Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hfe _ _ (2 * d))
  have h := ConcreteCategory.congr_hom hm (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x')
  change Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hp (2 * d)
    (Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d)
      (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x')) = _ at h
  have ho : Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d)
      (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x') =
        Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x :=
    Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := d) U x'
  rw [ho] at h
  exact h.trans (ProperImage.LocalOrientation.Constructions.Construction.complexCanonicalLocalClass_partialSourceMap_to d e x' y hey)

theorem canonicalLocalDual_pullback_localInverse
    (f : TopCat.of M ⟶ TopCat.of N) (x : M) (y : N) (hxy : f x = y)
    (hp : Set.MapsTo f ({x}ᶜ) ({y}ᶜ))
    (e : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N ω)
    (hx : x ∈ e.source) (he : Set.EqOn f e e.source) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hp (2 * d)
      (CanonicalLocalDual.Constructions.canonicalLocalDual d y) = CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  apply CanonicalLocalDual.Constructions.canonicalLocalDual_unique
  rw [AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality,
    localClass_map d f x y hxy hp e hx he, CanonicalLocalDual.Constructions.canonicalLocalDual_integralEvaluation]

end AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.Canonical

end

end OAI
