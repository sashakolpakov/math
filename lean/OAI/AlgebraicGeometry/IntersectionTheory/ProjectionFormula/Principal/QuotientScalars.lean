import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

/-! # Quotient Scalars -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientScalars

noncomputable section

/-! A native surjection with principal kernel supplies the exact
quotient-ring scalar action on endpoint modules. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] (r : R) (φ : R →+* S)
  (hk : RingHom.ker φ = Ideal.span {r})

def map : Parameter.ScalarQuotient.Ring R r →+* S :=
  Ideal.Quotient.lift (Ideal.span {r}) φ hk.symm.le

theorem map_mk (a : R) : map R S r φ hk (Ideal.Quotient.mk _ a) = φ a := rfl

def ringEquiv (hφ : Function.Surjective φ) : Parameter.ScalarQuotient.Ring R r ≃+* S :=
  RingEquiv.ofBijective (map R S r φ hk) ⟨by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    rw [← hk, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hab,
    fun b => let ⟨a, ha⟩ := hφ b; ⟨Ideal.Quotient.mk _ a, ha⟩⟩

def module (N : ModuleCat.{u} S) : ModuleCat.{u} (Parameter.ScalarQuotient.Ring R r) :=
  (ModuleCat.restrictScalars (map R S r φ hk)).obj N

def restrictionIso (N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj (module R S r φ hk N) ≅
      (ModuleCat.restrictScalars φ).obj N :=
  (LinearEquiv.refl R ((ModuleCat.restrictScalars φ).obj N)).toModuleIso

def extendEquiv (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (e : QuotSMulTop r M ≃ₗ[R] (ModuleCat.restrictScalars φ).obj N) :
    (Parameter.ScalarQuotient.quotient R r).obj M ≃ₗ[Parameter.ScalarQuotient.Ring R r]
      module R S r φ hk N := by
  let Q := Parameter.ScalarQuotient.Ring R r
  let NQ := module R S r φ hk N
  let : Module R NQ := Module.compHom NQ (Ideal.Quotient.mk (Ideal.span {r}))
  let : IsScalarTower R Q NQ := IsScalarTower.of_compHom R Q NQ
  change QuotSMulTop r M ≃ₗ[Q] NQ
  exact e.extendScalarsOfSurjective (S := Q) Ideal.Quotient.mk_surjective

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientScalars
