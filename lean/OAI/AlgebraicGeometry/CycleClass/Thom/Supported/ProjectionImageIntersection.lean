import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Projection Image Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionImageIntersection.Constructions

noncomputable section

/-! The actual image-supported intersection cup satisfies compact-fiber
projection for the literal inverse image of an even base class. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions.RightFormula OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionEvenIntersection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Projection.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rightBound_of_supportEquality (X Z : TopCat.{0}) (A B : Set X) (K : Set Z) (D E : Set (X × Z))
    (hE : E = Prod.fst ⁻¹' A) (hb : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z B Kᶜ ⊆ D) :
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Z (B ∪ A) Kᶜ ⊆ D ∪ E := by
  subst E
  exact ProjectionEvenIntersection.Constructions.RightFormula.rightProjectCupBound X Z A B Kᶜ D hb

theorem imageIntersectionBound (X : TopCat.{0}) {M L P Q : Type} [TopologicalSpace M]
    (u : L → X × M) (b : Q → X) (z : P → X) (K : Set M) (hb : Set.range u ⊆ Set.range b ×ˢ K) :
    Set.range u ∩ Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z) ⊆
      (Set.range b ∩ Set.range z) ×ˢ K := by
  intro y hy
  have hz := (Set.ext_iff.mp (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z) y).mp hy.2
  exact ⟨⟨(hb hy.1).1, hz⟩, (hb hy.1).2⟩

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectComplement_evenIntersectionOn (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (K : Set M) (hK : IsCompact K)
    (D E : Set (X × M)) (hD : IsOpen D) (hEo : IsOpen E) (hE : E = Prod.fst ⁻¹' A)
    (hmap : Set.MapsTo ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) E A)
    (hb : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D) (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D (2 * (p + d)))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * q)) :
    ProjectionCup.Constructions.projectComplement d X (B ∪ A) K hK (D ∪ E)
      (rightBound_of_supportEquality X (TopCat.of M) A B K D E hE hb)
      (2 * (p + q)) (2 * ((p + d) + q)) (by omega)
      (Normal.IntersectionCup.Constructions.evenIntersectionCup (TopCat.of (X × M)) D E hD hEo (p + d) q c
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst (X := X) (Y := TopCat.of M)) hmap (2 * q) a)) =
    Normal.IntersectionCup.Constructions.evenIntersectionCup X B A hB hA p q
      (ProjectionCup.Constructions.projectComplement d X B K hK D hb (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm c) a := by
  subst E
  exact ProjectionEvenIntersection.Constructions.projectComplement_evenIntersection d X A B hA hB K hK D hD hb p q c a

theorem projectAt_imageIntersectionCup (X : TopCat.{0}) {L P Q : Type}
    (u : L → X × M) (b : Q → X) (z : P → X)
    (hu : IsOpen (Set.range u)ᶜ) (hb : IsOpen (Set.range b)ᶜ) (hz : IsOpen (Set.range z)ᶜ)
    (K : Set M) (hK : IsCompact K) (hbound : Set.range u ⊆ Set.range b ×ˢ K) (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) (Set.range u)ᶜ (2 * (p + d)))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (Set.range z)ᶜ (2 * q)) :
    ProjectionDegree.Constructions.projectAt d X (Set.range b ∩ Set.range z) K hK
      (Set.range u ∩ Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z))
      (imageIntersectionBound X u b z K hbound) (2 * (p + q)) (2 * ((p + d) + q)) (by omega)
      (ImageIntersectionCup.Constructions.imageIntersectionCup u (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z) hu
        (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z hz) (p + d) q c
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst (X := X) (Y := TopCat.of M))
          (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z) (2 * q) a)) =
    ImageIntersectionCup.Constructions.imageIntersectionCup b z hb hz p q
      (ProjectionDegree.Constructions.projectAt d X (Set.range b) K hK (Set.range u) hbound (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm c) a := by
  let v := ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z
  have hv := ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z hz
  have hvEq : (Set.range v)ᶜ = Prod.fst ⁻¹' (Set.range z)ᶜ :=
    ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_complement ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z
  have hB := CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo X (Set.range b) K (Set.range u) hbound
  have hE := projectComplement_evenIntersectionOn d X (Set.range z)ᶜ (Set.range b)ᶜ hz hb K hK
    (Set.range u)ᶜ (Set.range v)ᶜ hu hv hvEq (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (TopCat.prodFst (X := X) (Y := TopCat.of M)) z) hB p q c a
  have ht := Projection.Transport.Constructions.Class.projectComplement_transport d X ((Set.range b)ᶜ ∪ (Set.range z)ᶜ)
    (Set.range b ∩ Set.range z)ᶜ (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq b z) K hK
    ((Set.range u)ᶜ ∪ (Set.range v)ᶜ) (Set.range u ∩ Set.range v)ᶜ (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v)
    (rightBound_of_supportEquality X (TopCat.of M) (Set.range z)ᶜ (Set.range b)ᶜ K (Set.range u)ᶜ (Set.range v)ᶜ hvEq hB)
    (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo X (Set.range b ∩ Set.range z) K (Set.range u ∩ Set.range v)
      (imageIntersectionBound X u b z K hbound))
    (2 * (p + q)) (2 * (p + q)) (2 * ((p + d) + q)) (2 * ((p + d) + q)) rfl rfl (by omega) (by omega)
    (Normal.IntersectionCup.Constructions.evenIntersectionCup (TopCat.of (X × M)) (Set.range u)ᶜ (Set.range v)ᶜ hu hv (p + d) q c
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst (X := X) (Y := TopCat.of M))
        (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo ((TopCat.prodFst (X := X) (Y := TopCat.of M)) : TopCat.of (X × M) ⟶ X) z) (2 * q) a))
  rw [ProjectionCup.Constructions.projectAt_eq_complement, ProjectionCup.Constructions.projectAt_eq_complement, ImageIntersectionTo.Constructions.Normal.imageIntersectionCup_eq_even, ImageIntersectionTo.Constructions.Normal.imageIntersectionCup_eq_even]
  exact ht.trans (congrArg (Transport.Constructions.Class.supportDegreeTransport X (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq b z) rfl) hE)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionImageIntersection.Constructions
