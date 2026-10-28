import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport

/-! # Twist Evaluation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistEvaluation.CrystallineTwistIdentity

noncomputable section

/-! Evaluation formulas isolate the native Ext construction from its coefficient normalizations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u w

theorem ext_reflexive_isos (R : Type*) [CommRing R]
    {C : Type*} [Category* C] [Abelian C] [Linear R C] [HasExt.{w} C]
    {A B : C} (s : A ≅ A) (t : B ≅ B) (hs : s = Iso.refl A) (ht : t = Iso.refl B)
    {n : ℕ} (y : Ext A B n) : IntegralComparison.Etale.Frobenius.extIsoCongr R s t n y = y := by
  rw [hs, ht]
  change ((Ext.mk₀ (𝟙 A)).comp y (Nat.zero_add n)).comp (Ext.mk₀ (𝟙 B)) (Nat.add_zero n) = y
  rw [Ext.mk₀_id_comp, Ext.comp_mk₀_id]

theorem ext_identity_transport (R : Type*) [CommRing R]
    {C : Type*} [Category* C] [Abelian C] [Linear R C] [HasExt.{w} C] [EnoughInjectives C]
    {A B : C} (s : A ≅ A) (t : B ≅ B) (hs : s = Iso.refl A) (ht : t = Iso.refl B)
    {n : ℕ} (x : Ext A B n) :
    IntegralComparison.Etale.Frobenius.extIsoCongr R s t n (x.mapExactFunctor (𝟭 C)) = x := by
  rw [hs, ht]
  exact PeriodInvariants.ExtTransport.exactTransport_id R x

theorem ext_functor_eq_id (R : Type*) [CommRing R]
    {C : Type*} [Category* C] [Abelian C] [Linear R C] [HasExt.{w} C] [EnoughInjectives C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : F = 𝟭 C) {A B : C} (s : F.obj A ≅ A) (t : F.obj B ≅ B)
    (hs : s = eqToIso (congrArg (fun G : C ⥤ C => G.obj A) hF))
    (ht : t = eqToIso (congrArg (fun G : C ⥤ C => G.obj B) hF))
    {n : ℕ} (x : Ext A B n) : IntegralComparison.Etale.Frobenius.extIsoCongr R s t n (x.mapExactFunctor F) = x := by
  subst F
  rw [hs, ht]
  exact PeriodInvariants.ExtTransport.exactTransport_id R x

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}
  (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

theorem cohomologyMap_apply (n : ℕ) (x : IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f' n) :
    PeriodInvariants.CrystallineTwistCohomology.cohomologyMap e he he' h n x =
      IntegralComparison.Etale.Frobenius.extIsoCongr (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
        (PeriodInvariants.CrystallineTwistCohomology.constantTransport e he he' h)
        (PeriodInvariants.CrystallineTwistCohomology.structureTransport e he he' h) n
          (x.mapExactFunctor (PeriodInvariants.CrystallineTwistCohomology.twistedRestriction e he he' h)) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.TwistEvaluation.CrystallineTwistIdentity
