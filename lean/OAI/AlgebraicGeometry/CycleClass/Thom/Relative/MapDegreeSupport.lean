import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Map Degree Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.MapDegreeSupport.Constructions

noncomputable section

/-! Simultaneous degree and support transport commutes with an
actual relative-cohomology pullback. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions

theorem relativePairMap_degreeSupport {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A A' : Set X} {B B' : Set Y} (eA : A = A') (eB : B = B')
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') {n m : ℕ} (hd : n = m) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n ≫
      (eqToIso (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A k) hd) ≪≫
        eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S m) eA)).hom =
      (eqToIso (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B k) hd) ≪≫
        eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S m) eB)).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf' m := by
  subst m
  simpa only [eqToIso_refl, Iso.refl_trans] using HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality f eA eB hf hf' n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.MapDegreeSupport.Constructions
