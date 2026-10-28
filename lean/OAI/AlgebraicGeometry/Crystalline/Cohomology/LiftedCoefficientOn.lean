import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistedHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TwistedConjugation
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Lifted Coefficient On -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOn.LiftedCoefficientTwistHomology

noncomputable section

/-! # The prescribed coefficient lift intertwines the actual twisted homology action -/

open _root_.CategoryTheory

universe u

variable (W : Type u) [CommRing W] (e : W ≃+* W)
  (K : CochainComplex (ModuleCat.{u} W) ℕ)

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.lift W
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.smallRestriction W e
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.largeRestriction W e

theorem square (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) :
    HomologicalComplex.homologyMap (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e f) n ≫
        (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        (T).map (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).hom =
      (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).hom ≫
        (P).map (HomologicalComplex.homologyMap f n ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom) ≫
        (LiftedCoefficientLarge.LiftedCoefficientTwist.iso W e).hom.app (K.homology n) :=
  TwistedHomology.TwistedHomologyTransport.homology_square Q T P (LiftedCoefficientLarge.LiftedCoefficientTwist.iso W e) K f n

private theorem component_apply {M : ModuleCat.{u} W} (f : M ⟶ (Q).obj M) (x : M) :
    ((P).map f ≫ (LiftedCoefficientLarge.LiftedCoefficientTwist.iso W e).hom.app M).hom (ULift.up (ULift.up x)) =
      ULift.up (ULift.up (f.hom x)) := rfl

theorem on_lift (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) (x : K.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom
        (HomologicalComplex.homologyMap (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e f) n
          ((Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv (ULift.up (ULift.up x))))) =
    ULift.up (ULift.up ((Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom (HomologicalComplex.homologyMap f n x))) := by
  let c := Mapped.ComplexHomology.MappedComplexHomology.iso P K n
  let g := HomologicalComplex.homologyMap f n ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom
  let f' := HomologicalComplex.homologyMap (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e f) n ≫
    (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom
  let g' := (P).map g ≫ (LiftedCoefficientLarge.LiftedCoefficientTwist.iso W e).hom.app (K.homology n)
  have hs : f' ≫ (T).map c.hom = c.hom ≫ g' :=
    (Category.assoc (HomologicalComplex.homologyMap (LiftedCoefficientLarge.LiftedCoefficientTwist.map W e f) n)
      (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom
      ((T).map c.hom)).trans (square W e K f n)
  have hc := Module.TwistedConjugation.ModuleTwistedConjugation.apply
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).toRingHom c f' g' hs
    (ULift.up (ULift.up x))
  exact hc.trans (component_apply W e g x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOn.LiftedCoefficientTwistHomology
