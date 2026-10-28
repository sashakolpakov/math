import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorPairPullback

/-! # Slant Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantCup.Constructions

noncomputable section

/-! The slant projection formula for the actual two-support cup with a projection pullback. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorPairPullback.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cupComplementMapsTo (X Z : TopCat.{0}) (A B : Set X) (C : Set Z) :
    Set.MapsTo (𝟙 (TopCat.of (X × Z))) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (A ∪ B) C)
      (Prod.fst ⁻¹' A ∪ HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) := by
  intro z hz
  exact hz.elim (fun hab => hab.elim Or.inl (fun hb => Or.inr (Or.inl hb)))
    (fun hc => Or.inr (Or.inr hc))

def projectionCup (X Z : TopCat.{0}) (A B : Set X) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (A ∪ B) C) (p + q) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × Z)))
    (cupComplementMapsTo X Z A B C) (p + q)
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × Z)) (Prod.fst ⁻¹' A)
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) (hA.preimage continuous_fst)
      ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X × Z) ⟶ X)
        (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a) c)

theorem projectionCup_eq_graph (X Z : TopCat.{0}) (A B : Set X) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) q) :
    projectionCup X Z A B C hA hB hC p q a c =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SlantProjection.Constructions.projectionGraphMap X Z)
        (SlantProjection.Constructions.projectionGraphMapsTo X Z A B C) (p + q)
        (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of (X × Z)) A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)
          hA ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p q a c) := by
  have h := ExteriorPairPullback.Constructions.exterior_pullback_pairMap (TopCat.prodFst : TopCat.of (X × Z) ⟶ X)
    (𝟙 (TopCat.of (X × Z))) (Prod.fst ⁻¹' A) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)
    A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) (hA.preimage continuous_fst)
    ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) hA
    ((hB.preimage continuous_fst).union (hC.preimage continuous_snd))
    (fun _ hx => hx) (fun _ hx => hx) p q a c
  simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, CategoryTheory.id_apply] at h
  refine (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (X × Z))) (cupComplementMapsTo X Z A B C) (p + q)) h).symm.trans ?_
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (X × Z)))
    (ExteriorPairPullback.Constructions.pairMap (TopCat.prodFst : TopCat.of (X × Z) ⟶ X) (𝟙 (TopCat.of (X × Z))))
    (cupComplementMapsTo X Z A B C)
    (ExteriorPairPullback.Constructions.pairMapsTo (TopCat.prodFst : TopCat.of (X × Z) ⟶ X) (𝟙 (TopCat.of (X × Z)))
      (A := A) (B := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)
      (C := Prod.fst ⁻¹' A) (D := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C)
      (fun _ hx => hx) (fun _ hx => hx)) (p + q)) _

theorem slant_projection (X Z : TopCat.{0}) (A B : Set X) (C : Set Z)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) (q + r))
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Z C r) :
    Slant.Constructions.slant ℚ X Z (A ∪ B) C (p + q) r (p + (q + r)) (Nat.add_assoc p q r) b
      (projectionCup X Z A B C hA hB hC p (q + r) a c) =
      HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a (Slant.Constructions.slant ℚ X Z B C q r (q + r) rfl b c) := by
  exact (congrArg (Slant.Constructions.slant ℚ X Z (A ∪ B) C (p + q) r (p + (q + r))
    (Nat.add_assoc p q r) b) (projectionCup_eq_graph X Z A B C hA hB hC p (q + r) a c)).trans
    (SlantProjection.Constructions.slant_graph X Z A B C hA hB hC p q r a c b)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantCup.Constructions
