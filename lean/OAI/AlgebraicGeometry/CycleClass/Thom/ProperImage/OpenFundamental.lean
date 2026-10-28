import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.LocalOrientation

/-! # Open Fundamental -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.OpenFundamental.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
variable [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 N]

/-- An injective analytic local diffeomorphism preserves each canonical
complex local orientation class, even when its image is not the entire target. -/
theorem complexCanonicalLocalClass_injective_localDiffeomorph
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f) (x : M) :
    Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d) (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) =
      Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (f x) := by
  obtain ⟨e, hx, he⟩ := hl x
  let U := LocalOrientation.Constructions.Construction.analyticPartialSource e
  let x' : U := ⟨x, hx⟩
  let i : TopCat.of U ⟶ TopCat.of M := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)
  have hi : Set.MapsTo i ({x'} : Set U)ᶜ ({x} : Set M)ᶜ := by
    intro y hy heq
    exact hy (Subtype.ext heq)
  have hf' : Set.MapsTo f ({x} : Set M)ᶜ ({f x} : Set N)ᶜ := by
    intro y hy heq
    exact hy (hf heq)
  have hfe : i ≫ f = LocalOrientation.Constructions.Construction.analyticPartialSourceMap d e := by
    ext z
    exact he z.property
  have hmaps : Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d) ≫
      Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d) =
    Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMapTo (LocalOrientation.Constructions.Construction.analyticPartialSourceMap d e)
      (LocalOrientation.Constructions.Construction.analyticPartialSourceMap_injective d e) x' (f x) (he hx).symm (2 * d) :=
    (Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp i f hi hf' (2 * d)).trans
      (Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hfe _ _ (2 * d))
  have h := ConcreteCategory.congr_hom hmaps (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x')
  have ho : Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d)
      (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x') = Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x :=
    Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := d) U x'
  change Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d)
      (Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x')) = _ at h
  rw [ho] at h
  exact h.trans (LocalOrientation.Constructions.Construction.complexCanonicalLocalClass_partialSourceMap_to d e x' (f x) (he hx).symm)

/-- Consequently an injective analytic local diffeomorphism preserves
the actual compact-support fundamental class on every compact set. -/
theorem complexCompactFundamentalClass_injective_localDiffeomorph
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (K : Set M) (hK : IsCompact K) :
    Geometric.OpenFundamental.Cycles.injectiveSupportHomologyMap f hf K (2 * d) (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK) =
      Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (f '' K) (hK.image f.hom.continuous) :=
  Geometric.OpenFundamental.Cycles.complexCompactFundamentalClass_map_of_local d f hf
    (complexCanonicalLocalClass_injective_localDiffeomorph d f hf hl) K hK

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.OpenFundamental.Constructions.Construction
