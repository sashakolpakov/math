import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor
import Mathlib.LinearAlgebra.Span.Basic

/-! # Injective Restrictions -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveRestrictions.CrystallineInjectiveRestrictions

noncomputable section

/-!
# Extension of injective native sections across principal opens

An injective native Witt-module sheaf has surjective restriction along
each native monomorphism. In particular this applies to every principal
projection and every inclusion in an actual principal coefficient diagram.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

theorem surjective (I : Sheaf J V) [Injective I]
    {P Q : Site.Object p k X} (f : P ⟶ Q) [Mono f] :
    Function.Surjective (I.obj.map f.op) := by
  intro x
  let a : ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k) ⟶
      I.obj.obj (op P) := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  obtain ⟨b, hb⟩ := SheafInjective.SheafInjectiveRestrictions.exists_extension J f
    (ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k)) I a
  refine ⟨b 1, ?_⟩
  exact (congrArg (fun g => g 1) hb).trans (LinearMap.toSpanSingleton_apply_one _ _ x)

theorem principal_surjective (I : Sheaf J V) [Injective I]
    (Q : Site.Object p k X) (s : Q.thickening.ring) :
    Function.Surjective (I.obj.map (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s).op) :=
  surjective p k X I _

theorem coefficient_surjective (I : Sheaf J V) [Injective I]
    (Q : Site.Object p k X) {r s : PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring}
    (f : r ⟶ s) :
    Function.Surjective (I.obj.map ((CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).map f).op) := by
  have : Mono ((CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).map f) := by
    have h := CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X Q f
    have : Mono ((CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).map f ≫
        CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q s) := by
      change Mono (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q f ≫
        CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q s)
      rw [h]
      infer_instance
    exact mono_of_mono _ (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q s)
  exact surjective p k X I _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveRestrictions.CrystallineInjectiveRestrictions
