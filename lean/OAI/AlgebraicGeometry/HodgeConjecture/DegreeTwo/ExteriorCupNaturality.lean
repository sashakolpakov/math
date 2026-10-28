import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation

/-! # Exterior Cup Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupNaturality.Constructions

noncomputable section

/-! Naturality of the actual supported exterior cup under maps of both pairs. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

variable {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
variable {A : Set X} {A' : Set X'} {B : Set Y} {B' : Set Y'}

theorem productFirst_relativePullback (hf : Set.MapsTo f A A') (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X' A' p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X×Y) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      (A := Prod.fst ⁻¹' A) (B := Prod.fst ⁻¹' A') (fun _ hx => hf hx) p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X'×Y') ⟶ X')
        (A := Prod.fst ⁻¹' A') (B := A') (fun _ hx => hx) p a) := by
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ f hf p ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _
    (TopCat.prodFst : TopCat.of (X×Y) ⟶ X) _ p) a =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ (TopCat.prodFst : TopCat.of (X'×Y') ⟶ X') _ p ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) _ p) a
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

theorem productSecond_relativePullback (hg : Set.MapsTo g B B') (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' B' q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X×Y) ⟶ Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      (A := Prod.snd ⁻¹' B) (B := Prod.snd ⁻¹' B') (fun _ hx => hg hx) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X'×Y') ⟶ Y')
        (A := Prod.snd ⁻¹' B') (B := B') (fun _ hx => hx) q b) := by
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ g hg q ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _
    (TopCat.prodSnd : TopCat.of (X×Y) ⟶ Y) _ q) b =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ (TopCat.prodSnd : TopCat.of (X'×Y') ⟶ Y') _ q ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap _ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) _ q) b
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

theorem relativeExteriorCup_naturality
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X' A' p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' B' q) :
    ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      (RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) (p+q)
      (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X' Y' A' B' hA' hB' p q a b) := by
  rw [ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup, productFirst_relativePullback f g hf,
    productSecond_relativePullback f g hg]
  exact SupportCup.Constructions.twoSupportCohomologyCup_naturality (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
    (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) (Prod.fst ⁻¹' A') (Prod.snd ⁻¹' B')
    (hA'.preimage continuous_fst) (hB'.preimage continuous_snd)
    (fun _ hx => hf hx) (fun _ hx => hg hx) _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupNaturality.Constructions
