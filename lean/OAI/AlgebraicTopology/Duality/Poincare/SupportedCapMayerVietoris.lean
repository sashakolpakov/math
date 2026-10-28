import OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisSum
import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportRepresentatives
import OAI.AlgebraicTopology.Duality.Poincare.OpenMayerVietorisComponents

/-! # Supported Cap Mayer Vietoris -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportedCapMayerVietoris

noncomputable section

/-!
# The supported cap connecting identity on actual representatives

One simultaneous small relative cycle and the actual cochain connecting
representatives give the signed open-set Mayer--Vietoris identity. All
chains in this calculation lie in their stated subspaces.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Refining the same small chain to the union cover preserves its genuine
relative-cycle condition. -/
theorem smallSupportUnionRefinement_mem
    (X : TopCat.{0}) (U V K L : Set X) (n : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (K ∪ L)ᶜ).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∪ V) (K ∪ L)ᶜ).f n
        ((SmallSupportCover.smallSupportChainToUnion ℤ X U V K L).f n s)) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) n := by
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToUnion_integral_inclusion X U V K L) n) s
  change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∪ V) (K ∪ L)ᶜ).f n
      ((SmallSupportCover.smallSupportChainToUnion ℤ X U V K L).f n s) =
    (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f n s at hi
  rw [hi]
  exact hs

/-- The same fact for refinement to the intersection support. -/
theorem smallSupportIntersectionRefinement_mem
    (X : TopCat.{0}) (U V K L : Set X) (n : ℕ)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X n)
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L (K ∩ L)ᶜ).f n s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∩ L)ᶜ) n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (K ∩ L)ᶜ).f n
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∩ V) (K ∩ L)ᶜ).f n
        ((SmallSupportCover.smallSupportChainToIntersection ℤ X U V K L).f n s)) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∩ L)ᶜ) n := by
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (SmallSupportCover.smallSupportChainToIntersection_integral_inclusion X U V K L) n) s
  change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X (U ∩ V) (K ∩ L)ᶜ).f n
      ((SmallSupportCover.smallSupportChainToIntersection ℤ X U V K L).f n s) =
    (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X (SmallSupportCover.smallSupportCover X U V K L)).f n s at hi
  rw [hi]
  exact hs

/-- The intersection cap as an actual local rational cycle. -/
def smallSupportIntersectionCapCycle
    (X : TopCat.{0}) (U V K L : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ) p)
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q))
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L (K ∩ L)ᶜ).f (p + q) s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∩ L)ᶜ) (p + q)) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (U ∩ V : Set X))) q :=
  SmallSupportedCapClass.smallSupportedRelativeCapCycle X (U ∩ V) (K ∩ L)ᶜ p q c
    ((SmallSupportCover.smallSupportChainToIntersection ℤ X U V K L).f (p + q) s)
    (smallSupportIntersectionRefinement_mem X U V K L (p + q) s hs)

/-- The native open-set connecting homomorphism of the union cap is the
intersection cap, with precisely the degree-dependent cap-boundary sign. -/
theorem supportedCapMayerVietoris_chain_identity
    {X : TopCat.{0}} (U V : Opens X) (K L : Set X) (p q : ℕ)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ) p)
    (bK : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).X p)
    (bL : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).X p)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ) (p + 1))
    (s : (SmallSupportCover.smallSupportScalarChains ℤ X U V K L).X (p + q + 1))
    (hs : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L (K ∪ L)ᶜ).f (p + q + 1) s ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∪ L)ᶜ) (p + q + 1))
    (hi : (SmallSupportRepresentatives.smallSupportRelativeProjection X U V K L (K ∩ L)ᶜ).f ((p + 1) + q)
        (CapMayerVietorisChains.smallSupportChainCast X U V K L (by omega : p + q + 1 = (p + 1) + q) s) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X (K ∩ L)ᶜ) ((p + 1) + q))
    (hab : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f p bK -
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f p bL =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∪ L)ᶜ).f p a.val)
    (hdK : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ).f (p + 1)
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ).d p (p + 1) bK) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f (p + 1) c.val)
    (hdL : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Lᶜ).f (p + 1)
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Lᶜ).d p (p + 1) bL) =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (K ∩ L)ᶜ).f (p + 1) c.val) :
    OpenRational.openRationalMayerVietorisBoundary U V q
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊔ V))) (q + 1)
          (CapMayerVietorisSum.smallSupportUnionCapCycle X U V K L p (q + 1) a s hs)) =
      ((-1 : ℤ) ^ (p + 1)) •
        Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ↥(U ⊓ V))) q
          (smallSupportIntersectionCapCycle X U V K L (p + 1) q c
            (CapMayerVietorisChains.smallSupportChainCast X U V K L (by omega : p + q + 1 = (p + 1) + q) s) hi) := by
  apply OpenMayerVietorisComponents.openRationalMayerVietorisBoundary_eq_of_signed_components U V p q
    (CapMayerVietorisSum.smallSupportUnionCapCycle X U V K L p (q + 1) a s hs)
    (CapMayerVietorisChains.smallSupportLeftCap X U V K L p (q + 1) bK s)
    (-CapMayerVietorisChains.smallSupportRightCap X U V K L p (q + 1) bL s)
    (smallSupportIntersectionCapCycle X U V K L (p + 1) q c
      (CapMayerVietorisChains.smallSupportChainCast X U V K L (by omega : p + q + 1 = (p + 1) + q) s) hi)
  · have hU : TopCat.ofHom (ContinuousMap.inclusion (show U ≤ U ⊔ V from le_sup_left)) =
        AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.subset_union_left : (U : Set X) ⊆ (U : Set X) ∪ V) := by
      ext x
      rfl
    have hV : TopCat.ofHom (ContinuousMap.inclusion (show V ≤ U ⊔ V from le_sup_right)) =
        AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.subset_union_right : (V : Set X) ⊆ (U : Set X) ∪ V) := by
      ext x
      rfl
    rw [hU, hV]
    rw [map_neg, ← sub_eq_add_neg]
    exact CapMayerVietorisSum.smallSupportCap_union_eq_sub X U V K L p (q + 1) a.val bK bL s hab
  · exact CapMayerVietorisChains.smallSupportLeftCap_boundary X U V K L p q bK c.val s
      (SmallSupportRepresentatives.smallSupportUnionCycle_boundary_left X U V K L (p + q + 1) (p + q) s hs) hdK
  · rw [map_neg]
    exact congrArg Neg.neg (CapMayerVietorisChains.smallSupportRightCap_boundary X U V K L p q bL c.val s
      (SmallSupportRepresentatives.smallSupportUnionCycle_boundary_right X U V K L (p + q + 1) (p + q) s hs) hdL)

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportedCapMayerVietoris
