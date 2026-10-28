import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.Transport

/-! # Projection Even Intersection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions.RightFormula

/-! Compact-fiber projection of right cup multiplication by an even base
class, in the original order of both supports and both degrees. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup OAI.AlgebraicGeometry.CycleClass.Thom.Projection.CupEnlargement.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Projection.Transport.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rightProjectCupBound (X Z : TopCat.{0}) (A B : Set X) (C : Set Z) (D : Set (X × Z))
    (hD : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B C ⊆ D) :
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (B ∪ A) C ⊆ D ∪ Prod.fst ⁻¹' A := by
  intro z hz
  exact hz.elim (fun hba => hba.elim (fun hb => Or.inl (hD (Or.inl hb))) Or.inr)
    (fun hc => Or.inl (hD (Or.inr hc)))

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectComplement_rightFormula (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (K : Set M) (hK : IsCompact K)
    (D : Set (X × M)) (hD : IsOpen D)
    (hb : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D (q + 2 * d)) :
    ProjectionCup.Constructions.projectComplement d X (B ∪ A) K hK (D ∪ Prod.fst ⁻¹' A)
      (rightProjectCupBound X (TopCat.of M) A B Kᶜ D hb)
      (q + 2 * p) ((q + 2 * d) + 2 * p) (by omega)
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A) hD (hA.preimage continuous_fst)
        (q + 2 * d) (2 * p) c (Transport.Constructions.ProjectionRightCup.basePullback X (TopCat.of M) A (2 * p) a)) =
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B A hB hA q (2 * p)
      (ProjectionCup.Constructions.projectComplement d X B K hK D hb q (q + 2 * d) rfl c) a := by
  have h := Transport.Constructions.ProjectionRightCup.projectComplement_rightCup d X A B hA hB K hK D hD hb p q a c
  simp only [Transport.Constructions.Class.cupSwapTransport_eq_transport] at h
  have ht := Projection.Transport.Constructions.Class.projectComplement_transport d X (B ∪ A) (A ∪ B) (Set.union_comm B A) K hK
    (D ∪ Prod.fst ⁻¹' A) (Prod.fst ⁻¹' A ∪ D) (Set.union_comm D (Prod.fst ⁻¹' A))
    (rightProjectCupBound X (TopCat.of M) A B Kᶜ D hb)
    (Projection.CupEnlargement.Constructions.projectCupBound X (TopCat.of M) A B Kᶜ D hb)
    (q + 2 * p) (2 * p + q) ((q + 2 * d) + 2 * p) (2 * p + (q + 2 * d))
    (Nat.add_comm q (2 * p)) (Nat.add_comm (q + 2 * d) (2 * p)) (by omega) (Nat.add_assoc (2 * p) q (2 * d))
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A) hD (hA.preimage continuous_fst)
      (q + 2 * d) (2 * p) c (Transport.Constructions.ProjectionRightCup.basePullback X (TopCat.of M) A (2 * p) a))
  apply Transport.Constructions.Class.supportDegreeTransport_injective X (Set.union_comm B A) (Nat.add_comm q (2 * p))
  have hs := congrArg
    (ProjectionCup.Constructions.projectComplement d X (A ∪ B) K hK (Prod.fst ⁻¹' A ∪ D)
      (Projection.CupEnlargement.Constructions.projectCupBound X (TopCat.of M) A B Kᶜ D hb)
      (2 * p + q) (2 * p + (q + 2 * d)) (Nat.add_assoc (2 * p) q (2 * d)))
    (Transport.Constructions.Class.cupSwapTransport_eq_transport (TopCat.of (X × M)) (Prod.fst ⁻¹' A) D (2 * p) (q + 2 * d)
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A) hD (hA.preimage continuous_fst)
        (q + 2 * d) (2 * p) c (Transport.Constructions.ProjectionRightCup.basePullback X (TopCat.of M) A (2 * p) a)))
  exact ht.symm.trans (hs.symm.trans h)

theorem projectComplement_rightFormulaAt (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (K : Set M) (hK : IsCompact K)
    (D : Set (X × M)) (hD : IsOpen D)
    (hb : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D) (p q n : ℕ) (hn : q + 2 * d = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D n) :
    ProjectionCup.Constructions.projectComplement d X (B ∪ A) K hK (D ∪ Prod.fst ⁻¹' A)
      (rightProjectCupBound X (TopCat.of M) A B Kᶜ D hb)
      (q + 2 * p) (n + 2 * p) (by omega)
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A) hD (hA.preimage continuous_fst)
        n (2 * p) c (Transport.Constructions.ProjectionRightCup.basePullback X (TopCat.of M) A (2 * p) a)) =
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B A hB hA q (2 * p)
      (ProjectionCup.Constructions.projectComplement d X B K hK D hb q n hn c) a := by
  subst n
  exact projectComplement_rightFormula d X A B hA hB K hK D hD hb p q a c

end AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions.RightFormula

namespace AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions

/-! The compact-fiber projection formula for the actual even-degree
intersection cup, with the geometric codimensions retained. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions.RightFormula
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Projection.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectComplement_evenIntersection (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (K : Set M) (hK : IsCompact K)
    (D : Set (X × M)) (hD : IsOpen D)
    (hb : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D) (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D (2 * (p + d)))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * q)) :
    ProjectionCup.Constructions.projectComplement d X (B ∪ A) K hK (D ∪ Prod.fst ⁻¹' A)
      (RightFormula.rightProjectCupBound X (TopCat.of M) A B Kᶜ D hb)
      (2 * (p + q)) (2 * ((p + d) + q)) (by omega)
      (Normal.IntersectionCup.Constructions.evenIntersectionCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A) hD (hA.preimage continuous_fst)
        (p + d) q c (Transport.Constructions.ProjectionRightCup.basePullback X (TopCat.of M) A (2 * q) a)) =
    Normal.IntersectionCup.Constructions.evenIntersectionCup X B A hB hA p q
      (ProjectionCup.Constructions.projectComplement d X B K hK D hb (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm c) a := by
  rw [Intersection.TwoSupportCup.Constructions.evenIntersectionCup_eq_twoSupport, Intersection.TwoSupportCup.Constructions.evenIntersectionCup_eq_twoSupport]
  have ht := Projection.Transport.Constructions.Class.projectComplement_transport d X (B ∪ A) (B ∪ A) rfl K hK
    (D ∪ Prod.fst ⁻¹' A) (D ∪ Prod.fst ⁻¹' A) rfl
    (RightFormula.rightProjectCupBound X (TopCat.of M) A B Kᶜ D hb)
    (RightFormula.rightProjectCupBound X (TopCat.of M) A B Kᶜ D hb)
    (2 * p + 2 * q) (2 * (p + q)) (2 * (p + d) + 2 * q) (2 * ((p + d) + q))
    (Nat.mul_add 2 p q).symm (Nat.mul_add 2 (p + d) q).symm (by omega) (by omega)
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A) hD (hA.preimage continuous_fst)
      (2 * (p + d)) (2 * q) c (Transport.Constructions.ProjectionRightCup.basePullback X (TopCat.of M) A (2 * q) a))
  refine ht.trans ?_
  exact congrArg (Transport.Constructions.Class.supportDegreeTransport X rfl (Nat.mul_add 2 p q).symm)
    (RightFormula.projectComplement_rightFormulaAt d X A B hA hB K hK D hD hb q (2 * p) (2 * (p + d))
      (Nat.mul_add 2 p d).symm a c)

end AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions

end

end OAI
