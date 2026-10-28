import OAI.AlgebraicGeometry.Cycles.Functoriality.TraceDetection

/-! # Compact Projection -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.CompactProjection.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace

theorem relativeScalarHomologyMap_domain_congr
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A A' : Set X} {B : Set Y}
    (h : A = A') (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B) (n : ℕ) :
    eqToHom (congrArg (fun C => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X C n) h) ≫
      HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf') n =
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n := by
  subst A'
  simp only [eqToHom_refl, Category.id_comp]

/-- Excision with a compact set in an open subspace as the support index. -/
def openCompactHomologyIso {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) (K : Set U)ᶜ n ≅
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ n :=
  (eqToIso (congrArg (fun C => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) C n)
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_preimage_compl U K))).symm ≪≫
    CycleClass.Geometric.CompactRelativeTrace.Cycles.rationalCompactSupportExcisionHomologyIso X (U : Set X) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K).isCompact U.isOpen (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset U K) n

/-- The forward excision map is exactly inclusion of the relative pairs. -/
theorem openCompactHomologyIso_hom {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ) :
    (openCompactHomologyIso U K n).hom =
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X))
          (A := (K : Set U)ᶜ) (B := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) (by
            rintro x hx ⟨z, hz, he⟩
            exact hx ((Subtype.ext he) ▸ hz))) n := by
  dsimp only [openCompactHomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [CycleClass.Geometric.CompactRelativeTrace.Cycles.rationalCompactSupportExcisionHomologyIso_hom]
  exact relativeScalarHomologyMap_domain_congr _ (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_preimage_compl U K).symm _ _ n

/-- Including the open compact trace back into the ambient relative group
recovers the actual absolute-to-relative homology projection. -/
theorem openCompactRelativeTrace_projection {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace U K n ≫ (openCompactHomologyIso U K n).hom =
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) n := by
  let e := eqToIso (congrArg (fun C => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) C n)
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_preimage_compl U K))
  change (CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace X (U : Set X) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K).isCompact U.isOpen (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset U K) n ≫ e.hom) ≫
      (e.inv ≫ (CycleClass.Geometric.CompactRelativeTrace.Cycles.rationalCompactSupportExcisionHomologyIso X (U : Set X)
        (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K).isCompact U.isOpen
        (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset U K) n).hom) = _
  rw [Category.assoc, e.hom_inv_id_assoc]
  exact CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace_excision X (U : Set X) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)
    (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K).isCompact U.isOpen (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset U K) n

/-- A projection vanishes if and only if its open compact trace vanishes. -/
theorem openCompactRelativeTrace_eq_zero_iff {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace U K n a = 0 ↔
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) n a = 0 := by
  have h := ConcreteCategory.congr_hom (openCompactRelativeTrace_projection U K n) a
  change (openCompactHomologyIso U K n).hom (AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace U K n a) =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) n a at h
  constructor
  · intro ha
    rw [← h, ha, map_zero]
  · intro ha
    apply (openCompactHomologyIso U K n).toLinearEquiv.injective
    change (openCompactHomologyIso U K n).hom _ = (openCompactHomologyIso U K n).hom 0
    rw [h, ha, map_zero]

/-- Equality of open traces is equivalent to equality of ambient projections. -/
theorem openCompactRelativeTrace_eq_iff {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ)
    (a b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace U K n a = AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace U K n b ↔
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) n a =
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) n b := by
  have h (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :=
    ConcreteCategory.congr_hom (openCompactRelativeTrace_projection U K n) z
  change ∀ z, (openCompactHomologyIso U K n).hom (AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace U K n z) =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage U K : Set X)ᶜ) n z at h
  rw [← h a, ← h b]
  exact (openCompactHomologyIso U K n).toLinearEquiv.injective.eq_iff.symm

/-- Ordinary pushforward commutes with projection to relative homology
at the compact preimage of the target support. -/
theorem homologyPushforward_compactProjection
    {X Y : TopCat.{0}} (f : X ⟶ Y) (K : Set Y) (n : ℕ) :
    HomologicalComplex.homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f) n ≫
      HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y Kᶜ) n =
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X (f ⁻¹' K)ᶜ) n ≫
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n := by
  have h := congrArg (fun g : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X ⟶
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y Kᶜ => HomologicalComplex.homologyMap g n)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality ℚ f
      (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx))
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact (HomologicalComplex.homologyMap_comp
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y Kᶜ) n).symm.trans h.symm

/-- Ambient relative projections at compact sets away from a closed
algebraic set detect the class in the complementary homology degree. -/
theorem ordinaryHomology_eq_of_compactProjections_outside_closed
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : Closeds V.carrier) (p q : ℕ)
    (hpq : (p + p) + q = 2 * V.complexDimension)
    (hc : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ W → p < CycleClass.Geometric.DimensionCycles.dimensionCodimension V Z)
    (a b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology q)
    (hproj : ∀ L : Compacts V.analyticSpace,
      (L : Set V.analyticSpace) ⊆ TraceDetection.Construction.algebraicComplementOpen V W →
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) q a =
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) q b) :
    a = b := by
  apply TraceDetection.Construction.ordinaryHomology_eq_of_traces_outside_closed V W p q hpq hc a b
  intro K
  let U : Opens (TopCat.of V.analyticSpace) := TraceDetection.Construction.algebraicComplementOpen V W
  let L : Compacts V.analyticSpace := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) U K
  have hLU : (L : Set V.analyticSpace) ⊆ U :=
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := TopCat.of V.analyticSpace) U K
  have h := hproj L hLU
  exact (openCompactRelativeTrace_eq_iff (X := TopCat.of V.analyticSpace) U K q a b).mpr h

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.CompactProjection.Construction
