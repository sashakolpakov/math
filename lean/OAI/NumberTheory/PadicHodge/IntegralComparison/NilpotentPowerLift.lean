import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittNilpotentTargetLift

/-! # Nilpotent Power Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentPowerLift

noncomputable section

/-! A canonical multiplicative lift of p-power values from a quotient
modulo p into a p-nilpotent ring. This lifts units and is natural in
commuting quotient squares, which is what line-bundle cocycles need. -/

universe u v w t
variable (p : ℕ) [Fact p.Prime]
  {A : Type u} [CommRing A] (n : ℕ) (hn : (p : A) ^ (n + 1) = 0)

def modPLift : ModP A p →* A :=
  (PeriodInvariants.WittNilpotentTargetLift.levelEquiv p n hn).toMonoidHom.comp
    ((WittVector.ghostComponentModPPow (p := p) n).toMonoidHom.comp
      (WittVector.teichmuller p))

theorem modPLift_mk (a : A) :
    modPLift p n hn (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) = a ^ (p ^ n) := by
  change PeriodInvariants.WittNilpotentTargetLift.levelEquiv p n hn
    (WittVector.ghostComponentModPPow n
      (WittVector.teichmuller p (Ideal.Quotient.mk (Ideal.span {(p : A)}) a))) = _
  rw [← WittVector.map_teichmuller, WittVector.ghostComponentModPPow_map_mk,
    WittVector.ghostComponent_teichmuller]
  exact PeriodInvariants.WittNilpotentTargetLift.levelEquiv_mk p n hn _

variable {A₀ : Type v} [CommRing A₀] (ρ : A →+* A₀)
  (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})

def quotientEquiv : ModP A p ≃+* A₀ :=
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hρ)

omit [Fact (Nat.Prime p)] in
theorem quotientEquiv_mk (a : A) :
    quotientEquiv p ρ hρ hker (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) = ρ a := rfl

def lift : A₀ →* A :=
  (modPLift p n hn).comp (quotientEquiv p ρ hρ hker).symm.toMonoidHom

theorem lift_apply (a : A) : lift p n hn ρ hρ hker (ρ a) = a ^ (p ^ n) := by
  rw [← quotientEquiv_mk p ρ hρ hker a]
  change modPLift p n hn ((quotientEquiv p ρ hρ hker).symm
    (quotientEquiv p ρ hρ hker (Ideal.Quotient.mk _ a))) = _
  rw [RingEquiv.symm_apply_apply, modPLift_mk]

theorem reduction (a : A₀) : ρ (lift p n hn ρ hρ hker a) = a ^ (p ^ n) := by
  obtain ⟨a, rfl⟩ := hρ a
  rw [lift_apply, map_pow]

def units : A₀ˣ →* Aˣ := Units.map (lift p n hn ρ hρ hker)

theorem units_reduction (a : A₀ˣ) :
    Units.map ρ.toMonoidHom (units p n hn ρ hρ hker a) = a ^ (p ^ n) := by
  apply Units.ext
  exact reduction p n hn ρ hρ hker a.val

variable {B : Type w} [CommRing B] {B₀ : Type t} [CommRing B₀]
  (hnB : (p : B) ^ (n + 1) = 0) (τ : B →+* B₀)
  (hτ : Function.Surjective τ) (hkerτ : RingHom.ker τ = Ideal.span {(p : B)})
  (f : A →+* B) (f₀ : A₀ →+* B₀) (hsq : τ.comp f = f₀.comp ρ)

include hsq in
theorem naturality (a : A₀) :
    f (lift p n hn ρ hρ hker a) = lift p n hnB τ hτ hkerτ (f₀ a) := by
  obtain ⟨a, rfl⟩ := hρ a
  have h := RingHom.congr_fun hsq a
  change τ (f a) = f₀ (ρ a) at h
  rw [lift_apply, map_pow, ← h, lift_apply]

include hsq in
theorem units_naturality (a : A₀ˣ) :
    Units.map f.toMonoidHom (units p n hn ρ hρ hker a) =
      units p n hnB τ hτ hkerτ (Units.map f₀.toMonoidHom a) := by
  apply Units.ext
  exact naturality p n hn ρ hρ hker hnB τ hτ hkerτ f f₀ hsq a.val

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentPowerLift
