import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicStalk

/-! # Stalk Values -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkValues.AnalyticLocal

noncomputable section

/-! Evaluation in the actual holomorphic structure stalk agrees with
section evaluation; its nonzero values detect units. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

omit [FiniteDimensional ℂ E] in
theorem chartSectionGerm_value (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (x : M) (hx : x ∈ e.source) (U : Opens M) (hxU : x ∈ U)
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom (e x) (ChartStalkGerms.AnalyticLocal.chartSectionGerm e he x hx U hxU f) = f ⟨x, hxU⟩ := by
  change CoefficientMem.openCoefficientExtension (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) (ChartStalkGerms.AnalyticLocal.chartFunctionSection e he U f).val (e x) = _
  rw [CoefficientMem.openCoefficientExtension_apply (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) _ ⟨e x, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U hx hxU⟩]
  change f ⟨e.symm (e x), _⟩ = f ⟨x, hxU⟩
  apply congrArg f
  exact Subtype.ext (e.left_inv hx)

def manifoldStalkValue (x : M) : ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk E M x →+* ℂ :=
  (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom (chartAt E x x)).comp
    (ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv E M (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)).toRingHom

theorem manifoldStalkValue_germ (x : M) (U : Opens M) (hxU : x ∈ U)
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) :
    manifoldStalkValue x (TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of M)
      (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M).obj U x hxU f) = f ⟨x, hxU⟩ := by
  exact (congrArg (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom (chartAt E x x))
    (ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv_germ E M (chartAt E x) (chart_mem_atlas E x) x
      (mem_chart_source E x) U hxU f)).trans
        (chartSectionGerm_value (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x) U hxU f)

theorem manifoldStalk_isUnit_iff (x : M) (a : ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk E M x) :
    IsUnit a ↔ manifoldStalkValue x a ≠ 0 := by
  let e := ManifoldHolomorphicStalk.AnalyticLocal.chartStructureStalkEquiv E M (chartAt E x) (chart_mem_atlas E x) x (mem_chart_source E x)
  constructor
  · intro ha
    exact (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.isUnit_iff_value_ne_zero _ _).mp (ha.map e.toRingHom)
  · intro ha
    have h := ((ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.isUnit_iff_value_ne_zero _ (e a)).mpr ha).map e.symm.toRingHom
    change IsUnit (e.symm (e a)) at h
    rwa [RingEquiv.symm_apply_apply] at h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkValues.AnalyticLocal
