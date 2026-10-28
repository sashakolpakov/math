import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartStalkGerms
import OAI.AlgebraicGeometry.Comparison.Betti.CommRingStalkForget
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Manifold Holomorphic Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicStalk.AnalyticLocal

noncomputable section

/-! The original RingCat-valued holomorphic structure sheaf of a
finite-dimensional complex manifold has Noetherian local stalks.
The identification uses each actual atlas chart and section pullback. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

abbrev manifoldStructureStalk (x : M) : RingCat :=
  TopCat.Presheaf.stalk (C := RingCat) (X := TopCat.of M) (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M).obj x

def chartStructureStalkEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) : manifoldStructureStalk E M x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) :=
  (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ) x).trans
    (Holomorphic.ChartStalkGerms.AnalyticLocal.chartFunctionStalkEquiv e he x hx)

theorem chartStructureStalkEquiv_germ (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (U : Opens M) (hxU : x ∈ U)
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) :
    chartStructureStalkEquiv E M e he x hx (TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of M)
      (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M).obj U x hxU f) =
        Holomorphic.ChartStalkGerms.AnalyticLocal.chartSectionGerm e he x hx U hxU f :=
  (congrArg (Holomorphic.ChartStalkGerms.AnalyticLocal.chartFunctionStalkEquiv e he x hx)
    (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv_germ (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ) x U hxU f)).trans
      (Holomorphic.ChartStalkGerms.AnalyticLocal.chartStalkToGerm_germ e he x hx U hxU f)

instance manifoldStructureStalkCommRing (x : M) : CommRing (manifoldStructureStalk E M x) :=
  { (inferInstance : Ring (manifoldStructureStalk E M x)) with
    mul_comm := fun a b =>
      (chartStructureStalkEquiv E M (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)).injective
        (by rw [map_mul, map_mul, mul_comm]) }

theorem manifoldStructureStalk_noetherian (x : M) : IsNoetherianRing (manifoldStructureStalk E M x) := by
  let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (chartAt E x x)) := NoetherianHolomorphicGerms.AnalyticLocal.holomorphic_germ_noetherian _
  exact isNoetherianRing_of_ringEquiv _
    (chartStructureStalkEquiv E M (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)).symm

instance manifoldStructureStalkLocalRing (x : M) : IsLocalRing (manifoldStructureStalk E M x) :=
  (chartStructureStalkEquiv E M (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)).symm.isLocalRing

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicStalk.AnalyticLocal
