import OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity

/-! # Cup Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupNaturality.Constructions

noncomputable section

/-! Actual pair-map naturality for supported cups with independently
specified output complements and degrees. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cupTo_naturality {X Y : TopCat} (f : X ⟶ Y)
    (A B S : Set X) (A' B' S' : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (eS : A ∪ B = S) (eS' : A' ∪ B' = S')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (hfS : Set.MapsTo f S S')
    (p q n : ℕ) (hn : p + q = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y A' p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B' q) :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo X A B S hA hB eS p q n hn
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfA p a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfB q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfS n
      (EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo Y A' B' S' hA' hB' eS' p q n hn a b) := by
  cases eS
  cases eS'
  cases hn
  exact HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup_naturality X A B hA hB p q f A' B' hA' hB' hfA hfB a b

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupNaturality.Constructions
