import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOn
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.RestrictedHomology

/-! # Coefficient Twist Homology Inverse -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientTwistHomologyInverse.LiftedCoefficientTwistHomologyInverse

noncomputable section

/-! # The inverse coefficient-lift comparison preserves semilinear homology actions -/

open _root_.CategoryTheory

universe u

variable (W : Type u) [CommRing W] (e : W ≃+* W)
  (K : CochainComplex (ModuleCat.{u} W) ℕ)

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.lift W
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.smallRestriction W e
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.largeRestriction W e

theorem inverse (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) (x : K.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv.hom
      (ULift.up (ULift.up ((Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom.hom
        ((HomologicalComplex.homologyMap f n).hom x)))) =
      (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom.hom
        ((HomologicalComplex.homologyMap (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e f) n).hom
          ((Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv.hom (ULift.up (ULift.up x)))) := by
  let c := Mapped.ComplexHomology.MappedComplexHomology.iso P K n
  let y := (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom.hom
    ((HomologicalComplex.homologyMap (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e f) n).hom
      (c.inv.hom (ULift.up (ULift.up x))))
  have hl := congrArg c.inv.hom (LiftedCoefficientOn.LiftedCoefficientTwistHomology.on_lift W e K f n x)
  exact hl.symm.trans (ModuleCat.inv_hom_apply c y)

theorem semilinear (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map e.toRingHom K K) (n : ℕ) (x : K.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv.hom
      (ULift.up (ULift.up (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap f n x))) =
      RestrictedHomology.RestrictedHomologyAction.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).toRingHom
        (((P).mapHomologicalComplex (.up ℕ)).obj K)
        (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f)) n
        ((Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv.hom (ULift.up (ULift.up x))) := by
  have hc := congrArg (fun y : K.homology n =>
    (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv.hom (ULift.up (ULift.up y)))
    (Semilinear.HomologyRestriction.SemilinearHomologyRestriction.original f n x)
  exact hc.symm.trans ((inverse W e K (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) n x).trans
    (RestrictedHomology.RestrictedHomologyAction.apply (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).toRingHom
      (((P).mapHomologicalComplex (.up ℕ)).obj K)
      (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f)) n
      ((Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv.hom (ULift.up (ULift.up x)))).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientTwistHomologyInverse.LiftedCoefficientTwistHomologyInverse
