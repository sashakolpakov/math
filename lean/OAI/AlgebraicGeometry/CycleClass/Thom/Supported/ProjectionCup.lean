import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.CupEnlargement
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree

/-! # Projection Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions

noncomputable section

/-! The actual supported compact-fiber projection satisfies the cup projection formula for arbitrary closed supports. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.CupEnlargement.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

def projectComplement (X : TopCat.{0}) (B : Set X) (K : Set M) (hK : IsCompact K)
    (D : Set (X × M)) (hbound : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D)
    (p n : ℕ) (hn : p + 2 * d = n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D n →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B p :=
  (Relative.Slant.Constructions.slant ℚ X (TopCat.of M) B Kᶜ p (2 * d) n hn (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK)).comp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M))) hbound n).hom

theorem projectAt_eq_complement (X : TopCat.{0}) (S : Set X) (K : Set M) (hK : IsCompact K)
    (T : Set (X × M)) (hT : T ⊆ S ×ˢ K) (p n : ℕ) (hn : p + 2 * d = n) :
    ProjectionDegree.Constructions.projectAt d X S K hK T hT p n hn =
      projectComplement d X Sᶜ K hK Tᶜ (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo X S K T hT) p n hn := by
  subst n
  rfl

theorem projectComplement_cup (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (K : Set M) (hK : IsCompact K)
    (D : Set (X × M)) (hD : IsOpen D)
    (hbound : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D (q + 2 * d)) :
    projectComplement d X (A ∪ B) K hK (Prod.fst ⁻¹' A ∪ D)
      (Projection.CupEnlargement.Constructions.projectCupBound X (TopCat.of M) A B Kᶜ D hbound)
      (p + q) (p + (q + 2 * d)) (Nat.add_assoc p q (2 * d))
      (Projection.CupEnlargement.Constructions.basePullbackCup X (TopCat.of M) A D hA hD p (q + 2 * d) a c) =
      HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a
        (projectComplement d X B K hK D hbound q (q + 2 * d) rfl c) := by
  refine (congrArg (Relative.Slant.Constructions.slant ℚ X (TopCat.of M) (A ∪ B) Kᶜ (p + q) (2 * d)
    (p + (q + 2 * d)) (Nat.add_assoc p q (2 * d)) (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK))
    (Projection.CupEnlargement.Constructions.projectionCup_enlargement X (TopCat.of M) A B Kᶜ D hA hB hK.isClosed.isOpen_compl hD
      hbound p (q + 2 * d) a c).symm).trans ?_
  exact Relative.SlantCup.Constructions.slant_projection X (TopCat.of M) A B Kᶜ hA hB hK.isClosed.isOpen_compl p q (2 * d)
    a (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
      hbound (q + 2 * d) c) (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions
