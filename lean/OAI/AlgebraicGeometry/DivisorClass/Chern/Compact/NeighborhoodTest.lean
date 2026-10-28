import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence

/-! # Neighborhood Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NeighborhoodTest

noncomputable section

section

/-! Actual smooth real coefficient cutoffs equal one near a prescribed compact set. -/

open Set Filter
open scoped ContDiff SchwartzMap _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

theorem exists_real_coefficient_cutoff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      ∀ x ∈ K, η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  obtain ⟨ψ, hψc, hψs, _, hψnear⟩ := ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK hU hKU
  have hs : tsupport (fun z => (ψ z).re) ⊆ tsupport ψ :=
    tsupport_comp_subset (show Complex.re 0 = 0 from rfl) ψ
  refine ⟨fun z => (ψ z).re, Complex.reCLM.contDiff.comp (ψ.smooth ⊤),
    hψc.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hψs, ?_⟩
  intro x hx
  exact (hψnear x hx).mono (fun _ hy => congrArg Complex.re hy)

end

/-! Every point of an open Euclidean set has a compact real Schwartz test equal to one nearby. -/

open Set Filter
open scoped ContDiff SchwartzMap _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

theorem exists_real_schwartz_test_near {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ z, g z = Complex.ofReal (g z).re) ∧ g =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  obtain ⟨g, hg, hgs, hgr, hgn⟩ := ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    (isCompact_singleton : IsCompact ({x} : Set E)) hU (Set.singleton_subset_iff.mpr hx)
  exact ⟨g, hg, hgs, hgr, hgn x (Set.mem_singleton x)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.NeighborhoodTest
