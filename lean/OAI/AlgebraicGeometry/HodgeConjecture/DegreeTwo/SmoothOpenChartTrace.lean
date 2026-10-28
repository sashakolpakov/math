import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothPartialChartTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition

/-! # Smooth Open Chart Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothOpenChartTrace.Constructions

noncomputable section

/-! Native trace compatibility for a smooth chart on any actual open subdomain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [ChartedSpace (Fin p → ℂ) M] [ChartedSpace (Fin p → ℂ) N]

abbrev openChartHomeomorph (e : OpenPartialHomeomorph M N)
    (U : Opens M) (V : Opens N) (hU : (U : Set M) ⊆ e.source)
    (hV : e '' (U : Set M) = V) : U ≃ₜ V :=
  e.homeomorphOfImageSubsetSource hU hV

theorem openChartHomeomorph_contMDiff (e : OpenPartialHomeomorph M N)
    (U : Opens M) (V : Opens N) (hU : (U : Set M) ⊆ e.source)
    (hV : e '' (U : Set M) = V)
    (he : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e e.source) :
    ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ (openChartHomeomorph e U V hU hV) := by
  apply (ContMDiff.subtypeVal_comp_iff V (openChartHomeomorph e U V hU hV)).mp
  intro x
  have hx := (he x.val (hU x.property)).contMDiffAt (e.open_source.mem_nhds (hU x.property))
  exact hx.comp x contMDiff_subtype_val.contMDiffAt

theorem openChartHomeomorph_symm_contMDiff (e : OpenPartialHomeomorph M N)
    (U : Opens M) (V : Opens N) (hU : (U : Set M) ⊆ e.source)
    (hV : e '' (U : Set M) = V)
    (hei : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e.symm e.target) :
    ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ (openChartHomeomorph e U V hU hV).symm := by
  apply (ContMDiff.subtypeVal_comp_iff U (openChartHomeomorph e U V hU hV).symm).mp
  intro x
  have hxV : x.val ∈ e.target := by
    have hxV' : x.val ∈ (V : Set N) := x.property
    rw [← hV] at hxV'
    obtain ⟨y,hy,hyx⟩ := hxV'
    exact hyx ▸ e.map_source (hU hy)
  have hx := (hei x.val hxV).contMDiffAt (e.open_target.mem_nhds hxV)
  exact hx.comp x contMDiff_subtype_val.contMDiffAt

variable [T2Space M] [T2Space N]
variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]

theorem complexManifoldTrace_openHomeomorphExtension (U : Opens N) (e : M ≃ₜ U)
    (he : ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1 e)
    (hei : ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1 e.symm) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension
      ((TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of U) e).hom ≫
        CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) U)
      (U.isOpen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding) (2*p) ≫
        AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := N) = AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := M) := by
  rw [← OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_comp
    (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of U) e).hom
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) U) e.isOpenEmbedding
    U.isOpen.isOpenEmbedding_subtypeVal, Category.assoc,
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace, AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open,
    OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_homeomorph]
  apply (cancel_epi (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of M) (Y := TopCat.of U) e (2*p)).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension.complexManifoldTrace_homeomorphIso p e he hei).symm

theorem complexManifoldTrace_openChartExtension (e : OpenPartialHomeomorph M N)
    (U : Opens M) (V : Opens N) (hU : (U : Set M) ⊆ e.source)
    (hV : e '' (U : Set M) = V)
    (he : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e.symm e.target) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension
      ((TopCat.isoOfHomeo (X := TopCat.of U) (Y := TopCat.of V)
        (openChartHomeomorph e U V hU hV)).hom ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) V)
      (V.isOpen.isOpenEmbedding_subtypeVal.comp
        (openChartHomeomorph e U V hU hV).isOpenEmbedding) (2*p) ≫
        AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := N) = AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := U) :=
  complexManifoldTrace_openHomeomorphExtension V (openChartHomeomorph e U V hU hV)
    ((openChartHomeomorph_contMDiff e U V hU hV he).of_le (by simp))
    ((openChartHomeomorph_symm_contMDiff e U V hU hV hei).of_le (by simp))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothOpenChartTrace.Constructions
