import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedMap
import OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward
import OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps

/-! # Ringed Stalk Charts -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedStalkCharts.AnalyticLocal

noncomputable section

section

/-! The original holomorphic ringed stalk map is actual composition of germs in manifold charts. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Filter
open scoped _root_.Topology _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedMap OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward.Local

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
  (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
  (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
  (k : OpenPartialHomeomorph N F) (hk : k ∈ atlas F N)
  (x : M) (hx : x ∈ e.source) (hgx : g x ∈ k.source)
  (hΦ : ContDiffAt ℂ ω (fun z => k (g (e.symm z))) (e x))

theorem chartStructureStalkEquiv_pullback (a : ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk F N (g x)) :
    ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv E M e he x hx
      (Module.RingedStalkPushforward.Local.ringedStalkMap (TopCat.ofHom ⟨g, hg.continuous⟩)
        (RingedMap.manifoldHolomorphicStructureMap g hg).hom x a) =
    LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt (fun z => k (g (e.symm z))) (e x) hΦ (k (g x))
      (by rw [e.left_inv hx]) (ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv F N k hk (g x) hgx a) := by
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := RingCat) (X := TopCat.of N)
    (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf F N).obj a
  change C^∞⟮𝓘(ℂ, F), U; 𝓘(ℂ), ℂ⟯ at a
  erw [Module.RingedStalkPushforward.Local.ringedStalkMap_germ, ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv_germ, ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv_germ]
  apply Subtype.ext
  erw [LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt_val]
  apply Germ.coe_eq.mpr
  let V : Opens M := (Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj U
  let W : Opens M := (Opens.map (TopCat.ofHom ⟨g, hg.continuous⟩)).obj ⟨k.source, k.open_source⟩
  have hxVW : x ∈ V ⊓ W := ⟨hxU, hgx⟩
  filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e (V ⊓ W)).isOpen.mem_nhds
    (Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e (V ⊓ W) hx hxVW)] with z hz
  have hzV : z ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V := ⟨hz.1, hz.2.1⟩
  have hgz : g (e.symm z) ∈ k.source := hz.2.2
  have hkz : k (g (e.symm z)) ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen k U :=
    Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen k U hgz hz.2.1
  change CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V)
      (ChartStalkGerms.AnalyticLocal.chartFunctionSection e he V _).val z =
    CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen k U) (ChartStalkGerms.AnalyticLocal.chartFunctionSection k hk U a).val
      (k (g (e.symm z)))
  rw [CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V) _ ⟨z, hzV⟩,
    CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen k U) _ ⟨k (g (e.symm z)), hkz⟩]
  change a ⟨g (e.symm z), _⟩ = a ⟨k.symm (k (g (e.symm z))), _⟩
  apply congrArg a
  exact Subtype.ext (k.left_inv hgz).symm

end

/-! Chart identifications of actual structure stalks, with explicitly normalized germ centers. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedMap OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward.Local

def chartStructureStalkEquivAt
    (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (u : E) (hu : e x = u) :
    ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk E M x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm u :=
  (ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv E M e he x hx).trans (GermMaps.AnalyticLocal.holomorphicGermPointEquiv hu)

theorem chartStructureStalkEquivAt_pullback
    {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
    (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (k : OpenPartialHomeomorph N F) (hk : k ∈ atlas F N)
    (x : M) (hx : x ∈ e.source) (hgx : g x ∈ k.source)
    (u : E) (hu : e x = u) (v : F) (hv : k (g x) = v)
    (hΦ : ContDiffAt ℂ ω (fun z => k (g (e.symm z))) u)
    (a : ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk F N (g x)) :
    chartStructureStalkEquivAt E M e he x hx u hu
      (Module.RingedStalkPushforward.Local.ringedStalkMap (TopCat.ofHom ⟨g, hg.continuous⟩)
        (RingedMap.manifoldHolomorphicStructureMap g hg).hom x a) =
    LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt (fun z => k (g (e.symm z))) u hΦ v
      (by rw [← hu, e.left_inv hx, hv])
      (chartStructureStalkEquivAt F N k hk (g x) hgx v hv a) := by
  subst u
  subst v
  exact chartStructureStalkEquiv_pullback g hg e he k hk x hx hgx hΦ a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedStalkCharts.AnalyticLocal
