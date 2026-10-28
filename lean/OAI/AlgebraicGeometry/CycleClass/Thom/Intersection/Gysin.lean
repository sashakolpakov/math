import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSupportedCup

/-! # Gysin -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions

noncomputable section

/-! Intersection with a closed complex immersion is its genuine
supported Thom pushforward applied to the pulled-back class. This
formula retains the intersection support and needs no transversality. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSupportedCup.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal
  TwoSupportCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) V.analyticSpace
    (Set.range Z.regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
  {L : Type} (v : L → V.analyticSpace) (hv : IsOpen (Set.range v)ᶜ)

def intersectionGysinIso :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
      (Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (2 * q) ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range Z.regularComplementInclusion ∩ Set.range v)ᶜ (2 * (p + q)) :=
  Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha ⟨(Set.range v)ᶜ, hv⟩ (2 * q) ≪≫
    eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Set.range Z.regularComplementInclusion)ᶜ ∪ (Set.range v)ᶜ) n) (Nat.mul_add 2 p q).symm) ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace S
      (2 * (p + q))) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v))

theorem imageIntersectionCup_eq_gysin_pullback
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace (Set.range v)ᶜ (2 * q)) :
    ImageIntersectionCup.Constructions.imageIntersectionCup Z.regularComplementInclusion v
      Z.closed.isClosed_range.isOpen_compl hv p q Z.regularThomClass b =
    (intersectionGysinIso Z a ha v hv).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) Z.regularComplementTopCatMap
        (A := Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (B := (Set.range v)ᶜ)
        (fun _ hx => hx) (2 * q) b) := by
  rw [ImageIntersectionTo.Constructions.Normal.imageIntersectionCup_eq_even, TwoSupportCup.Constructions.evenIntersectionCup_eq_twoSupport]
  have hc := ConcreteCategory.congr_hom
    (Immersion.GlobalSupportedCup.Constructions.Construction.regularSourceThomSupportedGlobalIso_cup Z a ha ⟨(Set.range v)ᶜ, hv⟩ (2 * q)) b
  change (Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha ⟨(Set.range v)ᶜ, hv⟩ (2 * q)).hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) Z.regularComplementTopCatMap
      (A := Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (B := (Set.range v)ᶜ)
      (fun _ hx => hx) (2 * q) b) =
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup V.analyticSpace (Set.range Z.regularComplementInclusion)ᶜ (Set.range v)ᶜ
      Z.closed.isClosed_range.isOpen_compl hv (2 * p) (2 * q) Z.regularThomClass b at hc
  exact congrArg (fun t =>
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace S
      (2 * (p + q))) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v))
      (eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
        ((Set.range Z.regularComplementInclusion)ᶜ ∪ (Set.range v)ᶜ) n)
          (Nat.mul_add 2 p q).symm) t)) hc.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions
