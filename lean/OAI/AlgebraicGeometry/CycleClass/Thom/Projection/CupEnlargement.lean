import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantCup

/-! # Cup Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.CupEnlargement.Constructions

noncomputable section

/-! Enlarging a bounded support commutes with taking the actual cup product with a base pullback. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def basePullbackCup (X Z : TopCat.{0}) (A : Set X) (D : Set (X × Z))
    (hA : IsOpen A) (hD : IsOpen D) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z)) D q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z)) (Prod.fst ⁻¹' A ∪ D) (p + q) :=
  HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × Z)) (Prod.fst ⁻¹' A) D
    (hA.preimage continuous_fst) hD p q
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodFst : TopCat.of (X × Z) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a) c

theorem projectCupBound (X Z : TopCat.{0}) (A B : Set X) (C : Set Z) (D : Set (X × Z))
    (hD : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C ⊆ D) :
    Set.MapsTo (𝟙 (TopCat.of (X × Z))) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (A ∪ B) C)
      (Prod.fst ⁻¹' A ∪ D) := by
  intro z hz
  exact hz.elim (fun hab => hab.elim Or.inl (fun hb => Or.inr (hD (Or.inl hb))))
    (fun hc => Or.inr (hD (Or.inr hc)))

theorem projectionCup_enlargement (X Z : TopCat.{0}) (A B : Set X) (C : Set Z)
    (D : Set (X × Z)) (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hD : IsOpen D)
    (hbound : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C ⊆ D) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z)) D q) :
    Relative.SlantCup.Constructions.projectionCup X Z A B C hA hB hC p q a
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × Z))) hbound q c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × Z)))
        (projectCupBound X Z A B C D hbound) (p + q) (basePullbackCup X Z A D hA hD p q a c) := by
  have hn := HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup_naturality (TopCat.of (X × Z)) (Prod.fst ⁻¹' A)
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C) (hA.preimage continuous_fst)
    ((hB.preimage continuous_fst).union (hC.preimage continuous_snd)) p q
    (𝟙 (TopCat.of (X × Z))) (Prod.fst ⁻¹' A) D (hA.preimage continuous_fst) hD
    (fun _ hx => hx) hbound
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodFst : TopCat.of (X × Z) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a) c
  simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, CategoryTheory.id_apply] at hn
  refine (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (X × Z))) (Relative.SlantCup.Constructions.cupComplementMapsTo X Z A B C) (p + q)) hn).trans ?_
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (X × Z))) (𝟙 (TopCat.of (X × Z)))
    (Relative.SlantCup.Constructions.cupComplementMapsTo X Z A B C)
    (fun _ hz => hz.elim Or.inl (fun h => Or.inr (hbound h))) (p + q)) _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.CupEnlargement.Constructions
