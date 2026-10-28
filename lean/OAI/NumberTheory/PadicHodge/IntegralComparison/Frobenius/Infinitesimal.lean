import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Infinitesimal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Infinitesimal

noncomputable section

/-! The actual finite-field Frobenius identifies maps with the same
square-zero reduction. Its affine power map factors through the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction

universe u

variable (k : Type u) [Field k] [Fintype k]
  (C : CommRingCat.{u}) (κ : k →+* C)

def affineBase : k →+* Γ(Spec C, ⊤) := (Scheme.ΓSpecIso C).inv.hom.comp κ

theorem qPower_spec :
    AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (Spec C) (affineBase k C κ) =
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldPowerRingHom k κ)) := by
  apply Global.FrobeniusGeometry.hom_ext_appTop
  apply (CategoryTheory.cancel_mono (Scheme.ΓSpecIso C).hom).mp
  rw [Scheme.ΓSpecIso_naturality]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (Scheme.ΓSpecIso C).hom.hom
    ((AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (Spec C) (affineBase k C κ)).appTop s) =
      ((Scheme.ΓSpecIso C).hom.hom s) ^ Fintype.card k
  rw [AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius_appTop, map_pow]

theorem power_eq_zero_of_squareZero (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (x : C) (hx : x ∈ J) : AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldPowerRingHom k κ x = 0 := by
  have hx2 : x ^ 2 = 0 := by
    have hm : x * x ∈ J * J := Ideal.mul_mem_mul hx hx
    rw [← pow_two, hJ] at hm
    simpa only [Ideal.mem_bot, pow_two] using hm
  exact pow_eq_zero_of_le (Fintype.one_lt_card : 1 < Fintype.card k) hx2

def quotientPower (J : Ideal C) (hJ : J ^ 2 = ⊥) : C ⧸ J →+* C :=
  Ideal.Quotient.lift J (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldPowerRingHom k κ)
    (fun x hx => power_eq_zero_of_squareZero k C κ J hJ x hx)

theorem qPower_factor (J : Ideal C) (hJ : J ^ 2 = ⊥) :
    AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (Spec C) (affineBase k C κ) =
      Spec.map (CommRingCat.ofHom (quotientPower k C κ J hJ)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  rw [qPower_spec, ← Spec.map_comp]
  rfl

include κ in
theorem equal_after_frobenius_of_reduction (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (X : Scheme.{u}) (κX : k →+* Γ(X, ⊤)) (a b : Spec C ⟶ X)
    (hab : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ b) :
    a ≫ AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k X κX = b ≫ AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k X κX := by
  rw [← AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius_naturality k (Spec C) (affineBase k C κ) κX a,
    ← AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius_naturality k (Spec C) (affineBase k C κ) κX b,
    qPower_factor k C κ J hJ, Category.assoc, Category.assoc, hab]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Infinitesimal
