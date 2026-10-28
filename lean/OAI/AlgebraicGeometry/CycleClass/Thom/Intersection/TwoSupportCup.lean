import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Two Support Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions

noncomputable section

/-! The actual diagonal definition of intersection cup agrees with the
original two-support relative cup. This identifies the intersection
construction with the supported Thom projection formula. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem diagonal_first_relativePullback (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageIntersectionCup.Constructions.diagonalMap X)
      (A := A) (B := Prod.fst ⁻¹' A) (fun _ ha => ha) n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X × X) ⟶ X)
        (A := Prod.fst ⁻¹' A) (B := A) (fun _ ha => ha) n a) = a := by
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (ImageIntersectionCup.Constructions.diagonalMap X) (TopCat.prodFst : TopCat.of (X × X) ⟶ X)
    (A := A) (B := Prod.fst ⁻¹' A) (C := A) (fun _ ha => ha) (fun _ ha => ha) n) a
  exact h.trans (ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) X A n) a)

theorem diagonal_second_relativePullback (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageIntersectionCup.Constructions.diagonalMap X)
      (A := A) (B := Prod.snd ⁻¹' A) (fun _ ha => ha) n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodSnd : TopCat.of (X × X) ⟶ X)
        (A := Prod.snd ⁻¹' A) (B := A) (fun _ ha => ha) n a) = a := by
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (ImageIntersectionCup.Constructions.diagonalMap X) (TopCat.prodSnd : TopCat.of (X × X) ⟶ X)
    (A := A) (B := Prod.snd ⁻¹' A) (C := A) (fun _ ha => ha) (fun _ ha => ha) n) a
  exact h.trans (ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) X A n) a)

theorem diagonal_relativeExteriorCup (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageIntersectionCup.Constructions.diagonalMap X)
      (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B) (p + q) (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X X A B hA hB p q a b) =
      HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b := by
  have h := HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup_naturality X A B hA hB p q (ImageIntersectionCup.Constructions.diagonalMap X)
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (hA.preimage continuous_fst) (hB.preimage continuous_snd)
    (fun _ ha => ha) (fun _ hb => hb)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodFst : TopCat.of (X × X) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ ha => ha) p a)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodSnd : TopCat.of (X × X) ⟶ X)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hb => hb) q b)
  rw [diagonal_first_relativePullback X A p a, diagonal_second_relativePullback X B q b] at h
  exact h.symm

theorem evenIntersectionCup_eq_twoSupport (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B (2 * q)) :
    Normal.IntersectionCup.Constructions.evenIntersectionCup X A B hA hB p q a b =
      eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) n)
        (Nat.mul_add 2 p q).symm) (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB (2 * p) (2 * q) a b) := by
  unfold Normal.IntersectionCup.Constructions.evenIntersectionCup ExteriorImageCup.Constructions.Even.evenExteriorCup
  rw [← Normal.Product.Constructions.Class.relativeCohomologyMap_degreeCast (ImageIntersectionCup.Constructions.diagonalMap X) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo X A B)
    (Nat.mul_add 2 p q).symm, diagonal_relativeExteriorCup]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions
