import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairIndex
import OAI.AlgebraicTopology.Duality.Poincare.CompactOpenIndex

/-! # Canonical Cap Excision Class -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapExcisionClass

/-!
# Canonical compact-support classes under inverse excision

These are the actual canonical integral classes. The geometric excision
compatibility was proved from their pointwise complex orientations in
`OpenFundamentalClass`; here it is exposed with the degree transports and
compact-support indexing used by the cap Mayer--Vietoris construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Equal-degree transport preserves the already constructed canonical
class, independently of the proofs identifying that degree with `2*d`. -/
theorem complexCompactClassInDegree_cast {n m : ℕ} (h : n = m)
    (hn : n = 2 * d) (hm : m = 2 * d) (K : Compacts M) :
    (eqToHom (congrArg
      (fun j => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) (K : Set M)ᶜ j) h))
        (ComplexManifoldCap.complexCompactClassInDegree d n hn K) =
      ComplexManifoldCap.complexCompactClassInDegree d m hm K := by
  subst m
  rfl

/-- Excision into an open neighborhood preserves the canonical class in
any degree already identified with the real dimension. -/
theorem complexCompactClassInDegree_openExcision_hom
    (W : Opens M) (K : Set M) (hK : IsCompact K) (hKW : K ⊆ (W : Set M))
    (n : ℕ) (hn : n = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (W : Set M) K hK W.isOpen hKW n).hom
        (ComplexManifoldCap.complexCompactClassInDegree d (M := W) n hn
          ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (W : Set M)) ⁻¹' K,
            AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (W : Set M) K hK hKW⟩) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn ⟨K, hK⟩ := by
  subst n
  exact AlgebraicGeometry.CycleClass.Geometric.OpenFundamental.Cycles.complexCompactFundamentalClass_openExcision d W K hK hKW

/-- Inverse excision returns precisely the intrinsic canonical class on
the compact preimage in the open submanifold. -/
theorem complexCompactClassInDegree_openExcision_inv
    (W : Opens M) (K : Set M) (hK : IsCompact K) (hKW : K ⊆ (W : Set M))
    (n : ℕ) (hn : n = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (W : Set M) K hK W.isOpen hKW n).inv
        (ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn ⟨K, hK⟩) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := W) n hn
        ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (W : Set M)) ⁻¹' K,
          AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (W : Set M) K hK hKW⟩ := by
  rw [← complexCompactClassInDegree_openExcision_hom d W K hK hKW n hn,
    ModuleCat.inv_hom_apply]

/-- Restricting the actual canonical class from a larger compact support,
then applying inverse excision, gives the intrinsic class at the smaller support. -/
theorem complexCompactClassInDegree_restriction_openExcision_inv
    (W : Opens M) (K L : Set M) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hKW : K ⊆ (W : Set M)) (n : ℕ) (hn : n = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (W : Set M) K hK W.isOpen hKW n).inv
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M) hKL n
          (ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn ⟨L, hL⟩)) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := W) n hn
        ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (W : Set M)) ⁻¹' K,
          AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupport_preimage_isCompact (TopCat.of M) (W : Set M) K hK hKW⟩ := by
  exact (congrArg
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (W : Set M) K hK W.isOpen hKW n).inv
    (ComplexManifoldCap.complexCompactClassInDegree_restriction d (M := M) n hn
      (K := ⟨K, hK⟩) (L := ⟨L, hL⟩) hKL)).trans
    (complexCompactClassInDegree_openExcision_inv d W K hK hKW n hn)

/-- The inverse-excision statement in the exact native compact-inside-open
indexing used by compact-support stage cap maps. -/
theorem complexCompactClassInDegree_openExcision_preimage
    (W : Opens M) (K : W.compactsInside) (n : ℕ) (hn : n = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (W : Set M) (K.val : Set M)
        K.val.isCompact W.isOpen K.property n).inv
        (ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn K.val) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := W) n hn
        (CompactOpenIndex.openCompactPreimage (X := TopCat.of M) W K) :=
  complexCompactClassInDegree_openExcision_inv d W (K.val : Set M)
    K.val.isCompact K.property n hn

/-- The canonical class over a compact union, restricted to the compact
intersection and excised into the open intersection, is its intrinsic class. -/
theorem complexCompactClassInDegree_pairIntersection
    (U V : Opens M) (K : U.compactsInside × V.compactsInside)
    (n : ℕ) (hn : n = 2 * d) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) ((U ⊓ V : Opens M) : Set M)
        ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)
        (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val.isCompact (U ⊓ V).isOpen
        (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).property n).inv
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M)
          (show ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M) ⊆
            ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M) from
              fun _ hx => Or.inl hx.1) n
          (ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn
            (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val)) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := ↥(U ⊓ V)) n hn
        (CompactOpenIndex.openCompactPreimage (X := TopCat.of M) (U ⊓ V)
          (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K)) := by
  exact complexCompactClassInDegree_restriction_openExcision_inv d (U ⊓ V)
    ((CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val : Set M)
    ((CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val : Set M)
    (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).val.isCompact
    (CompactSupportDecomposition.compactPairUnion (X := TopCat.of M) U V K).val.isCompact
    (fun _ hx => Or.inl hx.1) (CompactSupportPairIndex.compactPairIntersection (X := TopCat.of M) U V K).property n hn

end OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapExcisionClass
