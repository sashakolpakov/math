import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportDegreeTransport
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapExcisionClass

/-! # Canonical Small Support Representative -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CanonicalSmallSupportRepresentative

noncomputable section

/-!
# One canonical small-chain representative for the cap connecting square

The already proved simultaneous smallification gives a single integral chain
representing the canonical compact-union class. Its restriction represents the
canonical compact-intersection class. The checked degree-transport comparison
preserves this identification in the degrees used by the cap boundary formula.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- One actual chain in the four-open small-chain complex represents both
the canonical union class and, after restriction and degree transport, the
canonical intersection class needed by the signed cap connecting square. -/
theorem exists_canonicalSmallSupportRepresentative
    (U V : Opens M) (K : U.compactsInside × V.compactsInside)
    (p q : ℕ) (hpq : p + (q + 1) = 2 * d) :
    ∃ (s : (SmallSupportCover.smallSupportScalarChains ℤ (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M)).X (p + q + 1))
      (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M)
        ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q + 1) s ∈
          Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
            ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q + 1)),
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
          ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q + 1)
        ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
          (K.1.val : Set M) (K.2.val : Set M)
          ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q + 1) s, hs⟩ =
        ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q + 1) (by omega)
          (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val ∧
      ∃ (hi : (SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
          (K.1.val : Set M) (K.2.val : Set M)
          ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ).f ((p + 1) + q)
          (CapMayerVietorisChains.smallSupportChainCast (TopCat.of M) (U : Set M) (V : Set M)
            (K.1.val : Set M) (K.2.val : Set M) (by omega : p + q + 1 = (p + 1) + q) s) ∈
          Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
            ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) ((p + 1) + q)),
        Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
            ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) ((p + 1) + q)
          ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
            (K.1.val : Set M) (K.2.val : Set M)
            ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ).f ((p + 1) + q)
            (CapMayerVietorisChains.smallSupportChainCast (TopCat.of M) (U : Set M) (V : Set M)
              (K.1.val : Set M) (K.2.val : Set M) (by omega : p + q + 1 = (p + 1) + q) s), hi⟩ =
          ComplexManifoldCap.complexCompactClassInDegree d (M := M) ((p + 1) + q) (by omega)
            (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val := by
  have hn : p + q + 1 = 2 * d := by omega
  have hn' : (p + 1) + q = 2 * d := by omega
  have hdeg : p + q + 1 = (p + 1) + q := by omega
  obtain ⟨s, hs, hclass, hrestrict⟩ := SmallSupportRepresentatives.exists_commonSmallSupportRepresentative
    (TopCat.of M) (U : Set M) (V : Set M) (K.1.val : Set M) (K.2.val : Set M)
    U.isOpen V.isOpen K.1.val.isCompact.isClosed K.2.val.isCompact.isClosed
    K.1.property K.2.property (p + q + 1)
    (ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q + 1) hn
      (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val)
  have hsub : ((K.1.val : Set M) ∩ (K.2.val : Set M)) ⊆
      ((K.1.val : Set M) ∪ (K.2.val : Set M)) := fun _ hx => Or.inl hx.1
  obtain ⟨hi, hiclass⟩ := hrestrict _ hsub
  have hiclass' : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
      ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ) (p + q + 1)
      ⟨(SmallSupportRepresentatives.smallSupportRelativeProjection (TopCat.of M) (U : Set M) (V : Set M)
        (K.1.val : Set M) (K.2.val : Set M)
        ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ).f (p + q + 1) s, hi⟩ =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q + 1) hn
        (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val :=
    hiclass.trans (ComplexManifoldCap.complexCompactClassInDegree_restriction d (M := M) (p + q + 1) hn
      (K := (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val)
      (L := (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val) hsub)
  refine ⟨s, hs, hclass, SmallSupportDegreeTransport.smallSupportProjectedCycle_cast_mem
    (TopCat.of M) (U : Set M) (V : Set M) (K.1.val : Set M) (K.2.val : Set M)
    ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ hdeg s hi, ?_⟩
  exact (SmallSupportDegreeTransport.smallSupportProjectedClass_cast_eqToHom
    (TopCat.of M) (U : Set M) (V : Set M) (K.1.val : Set M) (K.2.val : Set M)
    ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ hdeg s hi).trans
      ((congrArg (eqToHom (congrArg
        (fun i => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M)
          ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)ᶜ).homology i) hdeg))
        hiclass').trans (CanonicalCapExcisionClass.complexCompactClassInDegree_cast d hdeg hn hn'
          (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val))

end

end OAI.AlgebraicTopology.Duality.Poincare.CanonicalSmallSupportRepresentative
