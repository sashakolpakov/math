import OAI.AlgebraicTopology.FundamentalClass.RelativeCoefficients
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts

/-! # Projected Classes -/

namespace OAI.AlgebraicTopology.FundamentalClass.ProjectedClasses.IntegrationConstruction

noncomputable section

/-! Representative formulas for relative chain classes and chart transport.
The input chain need only become a cycle after relative projection. -/

open _root_.CategoryTheory Set
open OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def projectedClass (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n :=
  Cohomology.Singular.ChainRepresentatives.chainClass _ n ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c, hc⟩

theorem projectedClass_map {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (n : ℕ) (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n)
    (hd : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection Y B).f n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n c) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains Y B) n) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f hf n (projectedClass X A n c hc) =
      projectedClass Y B n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n c) hd := by
  change HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f hf) n (Cohomology.Singular.ChainRepresentatives.chainClass _ n _) = _
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass _ n)
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality f hf) n) c

def chartSourceToModel {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) :
    TopCat.of e.source ⟶ Y :=
  (TopCat.isoOfHomeo (X := TopCat.of e.source) (Y := TopCat.of e.target)
    e.toHomeomorphSourceTarget).hom ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y e.target

theorem chartSourceToModel_mapsTo {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y)
    (K : Set X) (hKs : K ⊆ e.source) :
    MapsTo (chartSourceToModel e) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ (e '' K)ᶜ := by
  intro x hx hy
  exact hx ((AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChart_sourceTarget_mem e K hKs x).mpr hy)

theorem compactSupportChartHomologyIso_from_source {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X e.source K hK e.open_source hKs n).hom ≫
      (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso e K hK hKs n).hom =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (chartSourceToModel e) (chartSourceToModel_mapsTo e K hKs) n := by
  rw [AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso_hom, CategoryTheory.Iso.hom_inv_id_assoc]
  simp only [AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartSourceTargetIso, AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.homeomorphSupportHomologyIso,
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyIso_hom, AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso_hom]
  unfold AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionChainMap AlgebraicGeometry.CycleClass.Geometric.LocalExcision.Cycles.relativeCoverInclusion
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap_comp]
  rfl

theorem compactSupportChartHomologyIso_projectedClass {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of e.source)).X n)
    (hc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of e.source) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ).f n c ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of e.source) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ) n)
    (hambient : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source)).f n c) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Kᶜ) n)
    (hmodel : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection Y (e '' K)ᶜ).f n
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (chartSourceToModel e)).f n c) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains Y (e '' K)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso e K hK hKs n).hom
      (projectedClass X Kᶜ n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source)).f n c) hambient) =
      projectedClass Y (e '' K)ᶜ n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (chartSourceToModel e)).f n c) hmodel := by
  let hf : MapsTo (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ Kᶜ := fun _ h => h
  have hp := projectedClass_map (X := TopCat.of e.source) (Y := X)
    (A := ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ) (B := Kᶜ)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) hf n c hc hambient
  have h := ConcreteCategory.congr_hom
    (compactSupportChartHomologyIso_from_source e K hK hKs n)
    (projectedClass (TopCat.of e.source) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ n c hc)
  exact (congrArg (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso e K hK hKs n).hom hp.symm).trans
    (h.trans (projectedClass_map (X := TopCat.of e.source) (Y := Y)
      (A := ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ) (B := (e '' K)ᶜ)
      (chartSourceToModel e) (chartSourceToModel_mapsTo e K hKs) n c hc hmodel))

end

end OAI.AlgebraicTopology.FundamentalClass.ProjectedClasses.IntegrationConstruction
