import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Twist Equivalence -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistEquivalence.CrystallineTwistEquivalence

noncomputable section

/-! # The original crystalline base-twist functor is an equivalence -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
open OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction
open OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}
  (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

instance restriction_equivalence :
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.restriction (p := p) e he he' h).IsEquivalence := by
  let E := NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twistEquivalence (p := p) e he he' h
  let T := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)
  let U := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f')
  let : E.functor.IsCocontinuous T U := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous e he he' h
  let : E.inverse.IsCocontinuous U T :=
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.twist_cocontinuous e.symm he' he (NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.inverse_structure e h)
  let : E.inverse.IsDenseSubsite U T :=
    Equivalence.isDenseSubsite_inverse_of_isCocontinuous T U E
  let S := E.sheafCongr T U (ModuleCat.{u + 1} (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
  let i : S.inverse ≅ NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistRestriction.restriction e he he' h :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact Functor.isEquivalence_of_iso i

instance twistedRestriction_equivalence :
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) e he he' h).IsEquivalence := by
  unfold NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction
  infer_instance

theorem cohomologyMap_bijective (n : ℕ) :
    Function.Bijective (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (p := p) e he he' h n) := by
  let F := NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction (p := p) e he he' h
  let i := NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius.extIsoCongr (NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p) e he he' h) n
  exact i.bijective.comp
    (F.mapExt_bijective_of_preservesInjectiveObjects (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit f') (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf f') n)

theorem cohomologyMap_apply (n : ℕ)
    (x : NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f' n) :
    NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.cohomologyMap (p := p) e he he' h n x =
      (CategoryTheory.Abelian.Ext.mk₀ (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.constantTransport (p := p) e he he' h).inv).precomp
        (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf f) (zero_add n)
        ((CategoryTheory.Abelian.Ext.mk₀ (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.structureTransport (p := p) e he he' h).hom).postcomp
          ((NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction e he he' h).obj (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit f')) (add_zero n)
          (x.mapExactFunctor (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.twistedRestriction e he he' h))) :=
  CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistEquivalence.CrystallineTwistEquivalence
