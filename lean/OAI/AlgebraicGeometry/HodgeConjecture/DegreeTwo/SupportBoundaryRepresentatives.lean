import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SeparateSupportPrimitive
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupDifferential
import OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient

/-! # Support Boundary Representatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportBoundaryRepresentatives.Constructions

noncomputable section

/-! Identify the native support connecting map from genuine relative components and ambient differentials. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient

set_option backward.isDefEq.respectTransparency false

theorem relativeCochainInclusion_restriction_apply (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n a) = 0 :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction (ModuleCat.of ℚ ℚ) X A) n) a

theorem supportBoundary_eq_of_ambient_representatives
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∩ B)) n)
    (bA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n)
    (bB : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X n)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n+1))
    (hdiff : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n bA -
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n bB =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∩ B)).f n a.val)
    (hdA : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n+1)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n bA) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1) c.val) :
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A B hA hB n (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n a) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (n+1) c := by
  obtain ⟨aA,aB,u,hdiff₀,hdA₀,-,hclass⟩ := AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.supportConnecting_components X A B hA hB n a
  have hdA₁ : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n+1)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n aA) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1) u.val := by
    rw [← SupportCupDifferential.Constructions.relativeCochainInclusion_d_apply, hdA₀, AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient.relativeRationalSubsetCochainMap_inclusion_apply]
  let w := (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n bA -
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n aA
  have hwB : w = (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n bB -
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n aB := by
    calc
      w = ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n bA -
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n bB) -
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n aA -
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n aB) +
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n bB -
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f n aB) := by dsimp [w]; abel
      _ = _ := by rw [hdiff, hdiff₀, sub_self, zero_add]
  have hwA₀ : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n w = 0 := by
    dsimp only [w]
    rw [map_sub, relativeCochainInclusion_restriction_apply,
      relativeCochainInclusion_restriction_apply, sub_self]
  have hwB₀ : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f n w = 0 := by
    rw [hwB, map_sub, relativeCochainInclusion_restriction_apply,
      relativeCochainInclusion_restriction_apply, sub_self]
  have hw : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n+1) w =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1) (c-u).val := by
    dsimp only [w]
    rw [map_sub, hdA, hdA₁]
    exact (map_sub ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1)).hom c.val u.val).symm
  have hz := SeparateSupportPrimitive.Constructions.relative_class_zero_of_separate_primitive X A B hA hB n (c-u) w hwA₀ hwB₀ hw
  rw [map_sub] at hz
  exact hclass.trans (sub_eq_zero.mp hz).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportBoundaryRepresentatives.Constructions
