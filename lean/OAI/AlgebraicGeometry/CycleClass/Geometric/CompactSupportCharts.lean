import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts

/-! # Compact Support Charts -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts

noncomputable section

/-!
# Compact-support homology in actual charts

A compact subset contained in the source of an open partial homeomorphism
can be transported to the chart image. The comparison is the composite
of source excision, the actual source-to-target homeomorphism of pairs,
and target excision. Its point restrictions agree with the previously
constructed local chart comparisons.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- A homeomorphism carrying one support exactly onto another induces
the actual relative homology isomorphism for their complements. -/
def homeomorphSupportHomologyIso {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (K : Set X) (L : Set Y) (h : ∀ x, x ∈ K ↔ e x ∈ L) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X Kᶜ n ≅ LocalHomology.Cycles.relativeSingularHomology Y Lᶜ n :=
  LocalHomology.Cycles.relativeSingularHomologyIso e (fun x => not_congr (h x)) n

/-- Homeomorphism transport of support homology commutes with restriction
to the actual local group at every point of the support. -/
@[reassoc]
theorem homeomorphSupportHomologyIso_toPoint {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (K : Set X) (L : Set Y) (h : ∀ x, x ∈ K ↔ e x ∈ L)
    (n : ℕ) (x : X) (hx : x ∈ K) :
    (homeomorphSupportHomologyIso e K L h n).hom ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint Y L (e x) ((h x).mp hx) n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n ≫ (LocalHomology.Cycles.localSingularHomologyIso e x n).hom := by
  simp only [homeomorphSupportHomologyIso, LocalHomology.Cycles.localSingularHomologyIso,
    LocalHomology.Cycles.relativeSingularHomologyIso_hom, LocalHomologyPresheaf.Cycles.localHomologyToPoint]
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  unfold LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp, LocalHomology.Cycles.relativeSingularChainsMap_comp]
  simp only [Category.id_comp, Category.comp_id]

variable {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) (K : Set X)

/-- The image of a compact subset contained in the chart source is
compact in the model space. -/
theorem compactSupportChart_image_isCompact (hK : IsCompact K) (hKs : K ⊆ e.source) :
    IsCompact (e '' K) :=
  hK.image_of_continuousOn (e.continuousOn.mono hKs)

/-- A support lying in the chart source maps into the chart target. -/
theorem compactSupportChart_image_subset_target (hKs : K ⊆ e.source) :
    e '' K ⊆ e.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact e.map_source (hKs hx)

/-- On source and target subspaces, the chart homeomorphism carries
the support exactly onto the preimage of its ambient chart image. -/
theorem compactSupportChart_sourceTarget_mem (hKs : K ⊆ e.source) (x : e.source) :
    (x : X) ∈ K ↔ (e.toHomeomorphSourceTarget x : Y) ∈ e '' K := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hzx : z = (x : X) := e.injOn (hKs hz) x.property heq
    exact hzx ▸ hz

/-- The middle comparison is induced by the actual homeomorphism of
the chart source and target, with their actual support subsets. -/
def compactSupportChartSourceTargetIso (hKs : K ⊆ e.source) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of e.source)
        ((LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ n ≅
      LocalHomology.Cycles.relativeSingularHomology (TopCat.of e.target)
        ((LocalHomology.Cycles.subspaceInclusion Y e.target) ⁻¹' (e '' K))ᶜ n :=
  homeomorphSupportHomologyIso
    (X := TopCat.of e.source) (Y := TopCat.of e.target)
    e.toHomeomorphSourceTarget
    ((LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)
    ((LocalHomology.Cycles.subspaceInclusion Y e.target) ⁻¹' (e '' K))
    (compactSupportChart_sourceTarget_mem e K hKs) n

variable [T2Space X] [T2Space Y]

/-- Compact support contained in a chart source has the same actual
relative singular homology as its chart image in the model space. -/
def compactSupportChartHomologyIso (hK : IsCompact K) (hKs : K ⊆ e.source) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X Kᶜ n ≅ LocalHomology.Cycles.relativeSingularHomology Y (e '' K)ᶜ n :=
  (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X e.source K hK e.open_source hKs n).symm ≪≫
    compactSupportChartSourceTargetIso e K hKs n ≪≫
    CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso Y e.target (e '' K)
      (compactSupportChart_image_isCompact e K hK hKs) e.open_target
      (compactSupportChart_image_subset_target e K hKs) n

/-- The forward map explicitly uses inverse source excision, the chart
homeomorphism of pairs, and forward target excision. -/
theorem compactSupportChartHomologyIso_hom (hK : IsCompact K) (hKs : K ⊆ e.source)
    (n : ℕ) :
    (compactSupportChartHomologyIso e K hK hKs n).hom =
      (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X e.source K hK e.open_source hKs n).inv ≫
        (compactSupportChartSourceTargetIso e K hKs n).hom ≫
        (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso Y e.target (e '' K)
          (compactSupportChart_image_isCompact e K hK hKs) e.open_target
          (compactSupportChart_image_subset_target e K hKs) n).hom := rfl

/-- Transporting a compact-support class and then restricting at the
image point agrees with restricting first and applying the actual local
chart homology isomorphism. -/
@[reassoc]
theorem compactSupportChartHomologyIso_toPoint (hK : IsCompact K) (hKs : K ⊆ e.source)
    (n : ℕ) (x : X) (hx : x ∈ K) :
    (compactSupportChartHomologyIso e K hK hKs n).hom ≫
        LocalHomologyPresheaf.Cycles.localHomologyToPoint Y (e '' K) (e x) ⟨x, hx, rfl⟩ n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n ≫
        (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x (hKs hx) n).hom := by
  simp only [compactSupportChartHomologyIso, compactSupportChartSourceTargetIso,
    LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso_toPoint]
  have hmid := homeomorphSupportHomologyIso_toPoint
    (X := TopCat.of e.source) (Y := TopCat.of e.target)
    e.toHomeomorphSourceTarget
    ((LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)
    ((LocalHomology.Cycles.subspaceInclusion Y e.target) ⁻¹' (e '' K))
    (compactSupportChart_sourceTarget_mem e K hKs)
    n (⟨x, hKs hx⟩ : e.source) hx
  have hsource := CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso_inv_toPoint
    X e.source K hK e.open_source hKs x hx n
  have hleft := congrArg (fun f =>
    (CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso X e.source K hK e.open_source hKs n).inv ≫ f ≫
      (LocalExcision.Cycles.localExcisionHomologyIso Y e.target (e x) (e.map_source (hKs hx))
        e.open_target n).hom) hmid
  have hright := congrArg (fun f => f ≫
    (LocalHomology.Cycles.localSingularHomologyIso
      (X := TopCat.of e.source) (Y := TopCat.of e.target)
      e.toHomeomorphSourceTarget (⟨x, hKs hx⟩ : e.source) n).hom ≫
      (LocalExcision.Cycles.localExcisionHomologyIso Y e.target (e x) (e.map_source (hKs hx))
        e.open_target n).hom) hsource
  simp only [Category.assoc] at hleft hright
  exact hleft.trans hright

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts
