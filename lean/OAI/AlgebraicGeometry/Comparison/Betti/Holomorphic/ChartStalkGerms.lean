import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StandardFunctionSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

/-! # Chart Stalk Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartStalkGerms.AnalyticLocal

noncomputable section

section

/-! Holomorphic functions on manifold opens determine actual function
germs in a chart, compatibly with restriction. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def chartInverseToOpen (e : OpenPartialHomeomorph M E) (U : Opens M) :
    Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U → U := fun y => ⟨e.symm y, y.property.2⟩

theorem chartInverseToOpen_holomorphic (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (U : Opens M) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (chartInverseToOpen e U) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact ChartMaps.chartInverse_holomorphic e he (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen_le_target e U)

def chartFunctionSection (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ →+* FunctionPure.holomorphicFunctions (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) where
  toFun f := (StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U)).symm
    ⟨f ∘ chartInverseToOpen e U, f.property.comp (chartInverseToOpen_holomorphic e he U)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem chartFunctionSection_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (U : Opens M) (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) (y : Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) :
    (chartFunctionSection e he U f).val y = f ⟨e.symm y, y.property.2⟩ := rfl

def chartSectionGerm (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (U : Opens M) (hxU : x ∈ U) :
    C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) :=
  (SectionGerms.AnalyticLocal.holomorphicSectionGerm (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) (e x) (Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U hx hxU)).comp
    (chartFunctionSection e he U)

theorem chartSectionGerm_restrict (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) {U V : Opens M} (h : V ≤ U) (hxV : x ∈ V)
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) :
    chartSectionGerm e he x hx V hxV
      ((smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).map (homOfLE h).op f) =
        chartSectionGerm e he x hx U (h hxV) f := by
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [(Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V).isOpen.mem_nhds (Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e V hx hxV)] with y hy
  rw [CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V) _ ⟨y, hy⟩,
    CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) _ ⟨y, ⟨hy.1, h hy.2⟩⟩]
  rfl

end

section

/-! The actual manifold function stalk maps to the holomorphic germ
ring of each chart containing the point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def chartGermCocone (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of M) x).op ⋙
      smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ) where
  pt := CommRingCat.of (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x))
  ι :=
    { app := fun U => CommRingCat.ofHom (chartSectionGerm e he x hx U.unop.val U.unop.property)
      naturality := by
        intro U V f
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        exact chartSectionGerm_restrict e he x hx (leOfHom f.unop) V.unop.property a }

def chartStalkToGerm (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) :
    (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).stalk x →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) :=
  (colimit.desc _ (chartGermCocone e he x hx)).hom

theorem chartStalkToGerm_germ (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (U : Opens M) (hxU : x ∈ U)
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) :
    chartStalkToGerm e he x hx ((smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).germ U x hxU f) =
      chartSectionGerm e he x hx U hxU f := by
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (colimit.ι_desc (chartGermCocone e he x hx) (op ⟨U, hxU⟩))) f

end

section

/-! Equality of chart function germs implies equality in the actual
manifold structure stalk. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem chartStalkToGerm_injective (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) : Function.Injective (chartStalkToGerm e he x hx) := by
  intro a b hab
  obtain ⟨U, hxU, f, rfl⟩ := (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).exists_germ_eq a
  obtain ⟨V, hxV, g, rfl⟩ := (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).exists_germ_eq b
  change C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ at f
  change C^∞⟮𝓘(ℂ, E), V; 𝓘(ℂ), ℂ⟯ at g
  have hab' : chartSectionGerm e he x hx U hxU f = chartSectionGerm e he x hx V hxV g :=
    (chartStalkToGerm_germ e he x hx U hxU f).symm.trans
      (hab.trans (chartStalkToGerm_germ e he x hx V hxV g))
  have hfg := congrArg Subtype.val hab'
  change (CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) (chartFunctionSection e he U f).val :
    Germ (𝓝 (e x)) ℂ) =
      (CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V) (chartFunctionSection e he V g).val :
        Germ (𝓝 (e x)) ℂ) at hfg
  obtain ⟨W, hWeq, hW, hxW⟩ := mem_nhds_iff.mp (Germ.coe_eq.mp hfg)
  let T : Opens M := (U ⊓ V) ⊓ Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e ⟨W, hW⟩
  have hxT : x ∈ T := ⟨⟨hxU, hxV⟩, hx, hxW⟩
  have hTU : T ≤ U := fun _ h => h.1.1
  have hTV : T ≤ V := fun _ h => h.1.2
  apply (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).germ_ext T hxT
    (homOfLE hTU) (homOfLE hTV)
  apply ContMDiffMap.ext
  intro y
  have hy := hWeq y.property.2.2
  change CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) (chartFunctionSection e he U f).val (e y) =
    CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V) (chartFunctionSection e he V g).val (e y) at hy
  rw [CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) _
      ⟨e y, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U y.property.2.1 y.property.1.1⟩,
    CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e V) _
      ⟨e y, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e V y.property.2.1 y.property.1.2⟩] at hy
  change f ⟨e.symm (e y), _⟩ = g ⟨e.symm (e y), _⟩ at hy
  change f ⟨y, hTU y.property⟩ = g ⟨y, hTV y.property⟩
  simpa only [e.left_inv y.property.2.1] using hy

end

/-! Every holomorphic germ in a manifold chart comes from an actual
local manifold section. This identifies the native function stalk. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem chartSectionGerm_surjective (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x)) :
    ∃ (U : Opens M) (hxU : x ∈ U) (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯),
      chartSectionGerm e he x hx U hxU f = a := by
  obtain ⟨W, hxW, g, hg⟩ := SectionGerms.AnalyticLocal.exists_holomorphicSectionGerm (e x) a
  let U := Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W
  have hxU : x ∈ U := ⟨hx, hxW⟩
  let f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ :=
    ⟨(StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv E W g) ∘ ChartMaps.chartForward e W,
      (StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv E W g).property.comp (ChartMaps.chartForward_holomorphic e he W)⟩
  refine ⟨U, hxU, f, ?_⟩
  apply Eq.trans _ hg
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [W.isOpen.mem_nhds hxW, e.open_target.mem_nhds (e.map_source hx)] with y hyW hyt
  change y ∈ W at hyW
  have hyU : e.symm y ∈ U := ⟨e.map_target hyt, by
    change e (e.symm y) ∈ W
    rw [e.right_inv hyt]
    exact hyW⟩
  rw [CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) _ ⟨y, ⟨hyt, hyU⟩⟩,
    CoefficientMem.openCoefficientExtension_apply W _ ⟨y, hyW⟩]
  change g.val ⟨e (e.symm y), _⟩ = g.val ⟨y, hyW⟩
  apply congrArg g.val
  exact Subtype.ext (e.right_inv hyt)

theorem chartStalkToGerm_surjective (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) : Function.Surjective (chartStalkToGerm e he x hx) := by
  intro a
  obtain ⟨U, hxU, f, hf⟩ := chartSectionGerm_surjective e he x hx a
  exact ⟨(smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).germ U x hxU f,
    (chartStalkToGerm_germ e he x hx U hxU f).trans hf⟩

def chartFunctionStalkEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) :
    (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).stalk x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) :=
  RingEquiv.ofBijective (chartStalkToGerm e he x hx)
    ⟨chartStalkToGerm_injective e he x hx, chartStalkToGerm_surjective e he x hx⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartStalkGerms.AnalyticLocal
