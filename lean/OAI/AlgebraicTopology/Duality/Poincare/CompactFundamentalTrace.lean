import OAI.AlgebraicTopology.Duality.Poincare.CapRelativeTrace
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapExcisionClass

/-! # Compact Fundamental Trace -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace

noncomputable section

/-!
# Tracing the ordinary fundamental class to an open submanifold

The ordinary fundamental class of a compact complex manifold projects to
the canonical relative class over every compact support. Inverse excision
therefore gives the intrinsic compact fundamental class in any containing
open submanifold. Substitution into the proved cap--trace identity gives
the corresponding formula for every ordinary cohomology class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual compact-relative trace, indexed by a compact subset of the
open subspace itself. The final map only identifies the equal support sets. -/
def openCompactRelativeTrace {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n ⟶
      AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) (K : Set U)ᶜ n :=
  AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace X (U : Set X) (CompactSupportExcision.openSupportImage U K : Set X)
      (CompactSupportExcision.openSupportImage U K).isCompact U.isOpen (CompactSupportExcision.openSupportImage_subset U K) n ≫
    eqToHom (congrArg (fun A => AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) A n)
      (CompactSupportExcision.openSupportImage_preimage_compl U K))

/-- The local-support trace is the previously defined trace followed by
the proved image-preimage identification. -/
theorem openCompactRelativeTrace_apply {X : TopCat.{0}} [T2Space X]
    (U : Opens X) (K : Compacts U) (n : ℕ)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    openCompactRelativeTrace U K n z =
      (eqToHom (congrArg (fun A => AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of U) A n)
        (CompactSupportExcision.openSupportImage_preimage_compl U K)))
        (AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace X (U : Set X) (CompactSupportExcision.openSupportImage U K : Set X)
          (CompactSupportExcision.openSupportImage U K).isCompact U.isOpen (CompactSupportExcision.openSupportImage_subset U K) n z) := rfl

private theorem canonicalCompactCap_support_congr
    (d : ℕ) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace (Fin d → ℂ) Y] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 Y]
    {K L : Compacts Y} (h : K = L) (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Y) p) :
    (eqToHom (congrArg
        (fun T : Compacts Y => AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of Y) (T : Set Y)ᶜ q) h))
        (CapRelativeTrace.ordinaryRelativeCapHomology (TopCat.of Y) (K : Set Y)ᶜ
          K.isCompact.isClosed.isOpen_compl p q a
          (ComplexManifoldCap.complexCompactClassInDegree d (M := Y) (p + q) hpq K)) =
      CapRelativeTrace.ordinaryRelativeCapHomology (TopCat.of Y) (L : Set Y)ᶜ
        L.isCompact.isClosed.isOpen_compl p q a
        (ComplexManifoldCap.complexCompactClassInDegree d (M := Y) (p + q) hpq L) := by
  subst L
  rfl

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The ordinary fundamental class projects to the canonical relative
fundamental class over every compact support, with its actual degree cast. -/
theorem complexFundamentalClassInDegree_compactProjection
    (K : Compacts M) (N : ℕ) (hN : N = 2 * d) :
    HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (K : Set M)ᶜ) N
        (CompactMeaning.complexFundamentalClassInDegree d (M := M) N hN) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) N hN K := by
  have hπ :
      HomologicalComplex.homologyMap
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (Set.univ : Set M)ᶜ) N ≫
        AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M)
          (Set.subset_univ (K : Set M)) N =
      HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (K : Set M)ᶜ) N := by
    dsimp only [AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction]
    rw [← HomologicalComplex.homologyMap_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_projection]
  have h := ConcreteCategory.congr_hom hπ
    (CompactMeaning.complexFundamentalClassInDegree d (M := M) N hN)
  simp only [ConcreteCategory.comp_apply] at h
  rw [← h, CompactMeaning.complexFundamentalClassInDegree_projection]
  exact ComplexManifoldCap.complexCompactClassInDegree_restriction d (M := M) N hN
    (K := K) (L := ⊤) le_top

/-- Projecting the ordinary fundamental class to a compact support and
then applying inverse excision gives the intrinsic class in the open set. -/
theorem complexFundamentalClassInDegree_openExcision_inv
    (U : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (N : ℕ) (hN : N = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (U : Set M)
        K hK U.isOpen hKU N).inv
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) N
          (CompactMeaning.complexFundamentalClassInDegree d (M := M) N hN)) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := U) N hN
        ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' K,
          AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (U : Set M) K hK hKU⟩ := by
  have hp := complexFundamentalClassInDegree_compactProjection d (M := M) ⟨K, hK⟩ N hN
  change HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) N
    (CompactMeaning.complexFundamentalClassInDegree d (M := M) N hN) =
    ComplexManifoldCap.complexCompactClassInDegree d (M := M) N hN ⟨K, hK⟩ at hp
  rw [hp]
  exact CanonicalCapExcisionClass.complexCompactClassInDegree_openExcision_inv d U K hK hKU N hN

/-- In the geometric top degree the inverse-excised class is literally
the already constructed compact fundamental class of the open submanifold. -/
theorem complexManifoldFundamentalClass_openExcision_inv
    (U : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M)) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (U : Set M)
        K hK U.isOpen hKU (2 * d)).inv
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) (2 * d)
          (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d M)) =
      AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (M := U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' K)
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (U : Set M) K hK hKU) :=
  complexFundamentalClassInDegree_openExcision_inv d U K hK hKU (2 * d) rfl

/-- The same fundamental-class trace in the compact-inside-open indexing
used by compactly supported cohomology. -/
theorem complexFundamentalClassInDegree_openExcision_preimage
    (U : Opens M) (K : U.compactsInside) (N : ℕ) (hN : N = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (U : Set M) (K.val : Set M)
        K.val.isCompact U.isOpen K.property N).inv
        (HomologicalComplex.homologyMap
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (K.val : Set M)ᶜ) N
          (CompactMeaning.complexFundamentalClassInDegree d (M := M) N hN)) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := U) N hN
        (CompactOpenIndex.openCompactPreimage (X := M) U K) :=
  complexFundamentalClassInDegree_openExcision_inv d U (K.val : Set M)
    K.val.isCompact K.property N hN

/-- Every ordinary cohomology class has the expected cap trace: restrict
the class to the open submanifold and cap with its actual compact fundamental
class over the preimage support. -/
theorem complexManifoldOrdinaryCap_compactRelativeTrace
    (U : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace (TopCat.of M) (U : Set M) K hK U.isOpen hKU q
        (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq a) =
      CapRelativeTrace.ordinaryRelativeCapHomology (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' Kᶜ)
        (hK.isClosed.isOpen_compl.preimage
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)).hom.continuous) p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a)
        (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq
          ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' K,
            AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (U : Set M) K hK hKU⟩) := by
  rw [CompactMeaning.complexManifoldOrdinaryCap_apply, CapRelativeTrace.compactRelativeTrace_mixedSingularCapHomology,
    complexFundamentalClassInDegree_openExcision_inv d U K hK hKU (p + q) hpq]
  rfl

/-- The cap trace formula on the native compact-inside-open index. -/
theorem complexManifoldOrdinaryCap_compactRelativeTrace_preimage
    (U : Opens M) (K : U.compactsInside) (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace.Cycles.compactRelativeTrace (TopCat.of M) (U : Set M) (K.val : Set M)
        K.val.isCompact U.isOpen K.property q
        (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq a) =
      CapRelativeTrace.ordinaryRelativeCapHomology (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹' (K.val : Set M)ᶜ)
        (K.val.isCompact.isClosed.isOpen_compl.preimage
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)).hom.continuous) p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a)
        (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq
          (CompactOpenIndex.openCompactPreimage (X := M) U K)) :=
  complexManifoldOrdinaryCap_compactRelativeTrace d U (K.val : Set M)
    K.val.isCompact K.property p q hpq a

/-- The fundamental-class cap trace with its target indexed exactly by a
compact subset of the open submanifold, for every ordinary cohomology class. -/
theorem complexManifoldOrdinaryCap_openCompactRelativeTrace
    (U : Opens M) (K : Compacts U) (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    openCompactRelativeTrace (X := TopCat.of M) U K q
        (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq a) =
      CapRelativeTrace.ordinaryRelativeCapHomology (TopCat.of U) (K : Set U)ᶜ
        K.isCompact.isClosed.isOpen_compl p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a)
        (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq K) := by
  have h := complexManifoldOrdinaryCap_compactRelativeTrace d U
    (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K : Set M)
    (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K).isCompact
    (CompactSupportExcision.openSupportImage_subset (X := TopCat.of M) U K) p q hpq a
  rw [openCompactRelativeTrace_apply, h]
  let L : Compacts U :=
    ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ⁻¹'
        (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K : Set M),
      AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (U : Set M)
        (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K : Set M)
        (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K).isCompact
        (CompactSupportExcision.openSupportImage_subset (X := TopCat.of M) U K)⟩
  have hLK : L = K := Compacts.ext (CompactSupportExcision.openSupportImage_preimage (X := TopCat.of M) U K)
  exact canonicalCompactCap_support_congr d hLK p q hpq
    (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a)

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace
