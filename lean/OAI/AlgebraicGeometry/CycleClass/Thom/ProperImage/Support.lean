import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CompactProjection
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceCharacterization
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Support.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles

/-- A relative rational homology map vanishes when its full image lies
in the discarded subspace. -/
theorem relativeRationalHomologyMap_eq_zero_of_range_subset
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hAB : Set.MapsTo f A B) (hB : ∀ x, f x ∈ B) (n : ℕ) :
    HomologicalComplex.homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hAB) n = 0 := by
  have hz : IsZero (Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X Set.univ n) :=
    Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomology_isZero X Set.univ n (by
      simpa only [Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport, Set.compl_empty] using
        Geometric.CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X n)
  have hcomp := Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ (𝟙 X) f
    (A := A) (B := Set.univ) (C := B) (fun _ _ => trivial) (fun x _ => hB x) n
  simp only [Category.id_comp] at hcomp
  rw [← hcomp, hz.eq_of_tgt (HomologicalComplex.homologyMap
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (𝟙 X) (A := A) (B := Set.univ)
      (fun _ _ => trivial)) n) 0, zero_comp]

/-- Compact traces of a proper locally finite class vanish away from
the image of the proper map. -/
theorem properLocallyFiniteCompactTrace_eq_zero_of_disjoint
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Set Y) (hK : IsCompact K) (hd : ∀ x, f x ∉ K) (n : ℕ) :
    Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ f hf K hK n = 0 := by
  rw [Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace_def]
  have he := relativeRationalHomologyMap_eq_zero_of_range_subset f
    (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx) hd n
  exact (congrArg (fun t => Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ X
    (f ⁻¹' K) (hf.isCompact_preimage hK) n ≫ t) he).trans (comp_zero)

/-- The geometric fundamental class has zero compact projection
where the compact set is disjoint from the algebraic support. -/
theorem geometricCycleFundamentalClass_projection_eq_zero
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
    (L : Compacts V.analyticSpace)
    (hL : ∀ x ∈ (L : Set V.analyticSpace), x ∉ Set.range Z.analyticInclusion) :
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace)
        (L : Set V.analyticSpace)ᶜ) (2 * Z.regularComplexDimension)
      Z.geometricCycleFundamentalClass = 0 := by
  have hLU : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen := by
    intro x hx hs
    exact hL x hx (Z.analyticSingularBoundary_subset_range hs)
  let K : Compacts Z.regularAmbientSpace :=
    (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso Z.regularAmbientOpen).symm ⟨L, hLU⟩
  have himage : AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K = L :=
    congrArg Subtype.val ((AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso Z.regularAmbientOpen).apply_symm_apply ⟨L, hLU⟩)
  have ht : Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
      Z.geometricCycleFundamentalClass = 0 := by
    rw [Z.geometricCycleFundamentalClass_compactTrace]
    have hd : ∀ x, Z.regularComplementTopCatMap x ∉ (K : Set Z.regularAmbientSpace) := by
      intro x hx
      have hxL : Z.regularAnalyticToAmbient x ∈ (L : Set V.analyticSpace) := hx
      exact hL _ hxL (Z.range_regularAnalyticToAmbient_subset (Set.mem_range_self x))
    rw [properLocallyFiniteCompactTrace_eq_zero_of_disjoint
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap
      (K : Set Z.regularAmbientSpace) K.isCompact hd (2 * Z.regularComplexDimension)]
    rfl
  have hp := (CompactProjection.Constructions.Construction.openCompactRelativeTrace_eq_zero_iff
    (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K
      (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass).mp ht
  exact himage ▸ hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Support.Constructions.Construction
