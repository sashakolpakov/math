import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology

/-! # Lifted Coefficient Large -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist

noncomputable section

/-! # The prescribed coefficient lifts commute with semilinear restriction -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (W : Type u) [CommRing W]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)

def lift : ModuleCat.{u} W ⥤ ModuleCat.{u + 2} R :=
  BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W ⋙ ModuleCat.uliftFunctor.{u + 2, u + 1} R

instance lift_additive : (lift W).Additive := by
  unfold lift
  infer_instance

instance lift_preservesFiniteLimits : PreservesFiniteLimits (lift W) := by
  unfold lift
  exact comp_preservesFiniteLimits _ _

instance lift_preservesFiniteColimits : PreservesFiniteColimits (lift W) := by
  unfold lift
  exact comp_preservesFiniteColimits _ _

variable (e : W ≃+* W)

abbrev smallRestriction : ModuleCat.{u} W ⥤ ModuleCat.{u} W :=
  ModuleCat.restrictScalars e.toRingHom

abbrev largeRestriction : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} R :=
  ModuleCat.restrictScalars (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).toRingHom

def iso : smallRestriction W e ⋙ lift W ≅ lift W ⋙ largeRestriction W e :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def complexIso (K : CochainComplex (ModuleCat.{u} W) ℕ) :
    ((lift W).mapHomologicalComplex (.up ℕ)).obj
        (((smallRestriction W e).mapHomologicalComplex (.up ℕ)).obj K) ≅
      ((largeRestriction W e).mapHomologicalComplex (.up ℕ)).obj
        (((lift W).mapHomologicalComplex (.up ℕ)).obj K) :=
  (Functor.mapHomologicalComplexCompIso (iso W e) (.up ℕ)).app K

def map {K : CochainComplex (ModuleCat.{u} W) ℕ}
    (f : K ⟶ ((smallRestriction W e).mapHomologicalComplex (.up ℕ)).obj K) :
    ((lift W).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((largeRestriction W e).mapHomologicalComplex (.up ℕ)).obj
        (((lift W).mapHomologicalComplex (.up ℕ)).obj K) :=
  ((lift W).mapHomologicalComplex (.up ℕ)).map f ≫ (complexIso W e K).hom

theorem component {K : CochainComplex (ModuleCat.{u} W) ℕ}
    (f : K ⟶ ((smallRestriction W e).mapHomologicalComplex (.up ℕ)).obj K)
    (n : ℕ) (x : K.X n) :
    ((LiftedCoefficientTwist.map W e f).f n).hom (ULift.up (ULift.up x)) = ULift.up (ULift.up ((f.f n).hom x)) := rfl

instance map_quasiIso {K : CochainComplex (ModuleCat.{u} W) ℕ}
    (f : K ⟶ ((smallRestriction W e).mapHomologicalComplex (.up ℕ)).obj K) [QuasiIso f] :
    QuasiIso (LiftedCoefficientTwist.map W e f) := by
  unfold LiftedCoefficientTwist.map
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist
