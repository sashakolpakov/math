import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittZero

/-! # Witt Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittBase

noncomputable section

/-!
# IntegralComparison: bounded original crystalline objects have their native truncated Witt base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of (WittVector p k))}

local notation "W" => WittVector p k
local notation "WittIdeal" => Ideal.span {(p : W)}
local notation "wittDP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

variable (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
  (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f)
  (n : ℕ) (hn : (p : U.ring) ^ (n + 1) = 0)

omit [Fintype k] in
include hn in
theorem base_kills : WittIdeal ^ (n + 1) ≤ RingHom.ker U.base := by
  rw [Ideal.span_singleton_pow, Ideal.span_le]
  rintro a (rfl : a = _)
  change U.base ((p : W) ^ (n + 1)) = 0
  rw [map_pow, map_natCast, hn]

def truncatedBase : Truncated.Witt.Ring p k n →+* U.ring :=
  Ideal.Quotient.lift _ U.base (base_kills p k U n hn)

omit [Fintype k] in
theorem truncatedBase_quotient :
    (truncatedBase p k U n hn).comp (Truncated.Witt.quotient p k n) = U.base := by
  apply RingHom.ext
  intro w
  rfl

omit [Fintype k] in
theorem truncatedBase_isDPMorphism :
    DividedPowers.IsDPMorphism (Truncated.Witt.dividedPowers p k n) U.dividedPowers
      (truncatedBase p k U n hn) := by
  apply DividedPowers.IsDPMorphism.of_comp wittDP (Truncated.Witt.dividedPowers p k n)
    U.dividedPowers (Truncated.Witt.quotient p k n) (truncatedBase p k U n hn) rfl
    (Truncated.Witt.quotient_isDPMorphism p k n)
  rw [truncatedBase_quotient]
  exact U.baseCompatible

def residueBase (h : (p : U.ring) = 0) : k →+* U.ring :=
  (truncatedBase p k U 0 ((pow_one (p : U.ring)).trans h)).comp
    (Truncated.WittZero.residueEquiv p k).symm.toRingHom

theorem residueBase_constantCoeff (h : (p : U.ring) = 0) :
    (residueBase p k U h).comp WittVector.constantCoeff = U.base := by
  have he (w : W) : (Truncated.WittZero.residueEquiv p k).symm (WittVector.constantCoeff w) =
      Truncated.Witt.quotient p k 0 w := by
    apply (Truncated.WittZero.residueEquiv p k).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  apply RingHom.ext
  intro w
  change truncatedBase p k U 0 ((pow_one (p : U.ring)).trans h)
    ((Truncated.WittZero.residueEquiv p k).symm (WittVector.constantCoeff w)) = U.base w
  rw [he]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittBase
