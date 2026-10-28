import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PresentedAlgebra

/-! # Point Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations

noncomputable section

/-! The intrinsic complex vector space of derivations at an actual
algebra point is canonically its dual-number fiber. -/

variable {S : Type*} [CommRing S] [Algebra ℂ S]

def pointDerivations (x : S →ₐ[ℂ] ℂ) : Submodule ℂ (S →ₗ[ℂ] ℂ) where
  carrier D := D 1 = 0 ∧ ∀ a b, D (a * b) = x a * D b + x b * D a
  zero_mem' := by
    refine ⟨rfl, ?_⟩
    intro a b
    change (0 : ℂ) = x a * 0 + x b * 0
    ring
  add_mem' := by
    intro D E hD hE
    constructor
    · change D 1 + E 1 = 0
      rw [hD.1, hE.1, add_zero]
    · intro a b
      change D (a * b) + E (a * b) = x a * (D b + E b) + x b * (D a + E a)
      rw [hD.2, hE.2]
      ring
  smul_mem' := by
    intro c D hD
    constructor
    · change c • D 1 = 0
      rw [hD.1, smul_zero]
    · intro a b
      change c * D (a * b) = x a * (c * D b) + x b * (c * D a)
      rw [hD.2]
      ring

def derivationOfDualPoint (x : S →ₐ[ℂ] ℂ) (f : Dual.PresentedAlgebra.DualAlgebraPoints x) : pointDerivations x := by
  refine ⟨(TrivSqZeroExt.sndHom ℂ ℂ).comp f.val.toLinearMap, ?_, ?_⟩
  · change (f.val 1).snd = 0
    rw [map_one]
    rfl
  · intro a b
    change (f.val (a * b)).snd = x a * (f.val b).snd + x b * (f.val a).snd
    rw [map_mul, DualNumber.snd_mul]
    have ha : (f.val a).fst = x a := DFunLike.congr_fun f.property a
    have hb : (f.val b).fst = x b := DFunLike.congr_fun f.property b
    rw [ha, hb]
    ring

def dualPointOfDerivation (x : S →ₐ[ℂ] ℂ) (D : pointDerivations x) : Dual.PresentedAlgebra.DualAlgebraPoints x := by
  let f : S →ₐ[ℂ] DualNumber ℂ := {
    toFun := fun a => ⟨x a, D.val a⟩
    map_one' := TrivSqZeroExt.ext x.map_one D.property.1
    map_mul' := fun a b => TrivSqZeroExt.ext (x.map_mul a b) (by
      change D.val (a * b) = x a * D.val b + D.val a * x b
      rw [D.property.2]
      ring)
    map_zero' := TrivSqZeroExt.ext x.map_zero D.val.map_zero
    map_add' := fun a b => TrivSqZeroExt.ext (x.map_add a b) (D.val.map_add a b)
    commutes' := fun c => TrivSqZeroExt.ext (x.commutes c) (by
      change D.val (algebraMap ℂ S c) = 0
      rw [Algebra.algebraMap_eq_smul_one, D.val.map_smul, D.property.1, smul_zero]) }
  exact ⟨f, AlgHom.ext (fun _ => rfl)⟩

def dualPointDerivationsEquiv (x : S →ₐ[ℂ] ℂ) : Dual.PresentedAlgebra.DualAlgebraPoints x ≃ pointDerivations x where
  toFun := derivationOfDualPoint x
  invFun := dualPointOfDerivation x
  left_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    exact TrivSqZeroExt.ext (DFunLike.congr_fun f.property a).symm rfl
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    rfl

theorem dualPointDerivationsEquiv_apply (x : S →ₐ[ℂ] ℂ) (f : Dual.PresentedAlgebra.DualAlgebraPoints x) (a : S) :
    (dualPointDerivationsEquiv x f).val a = (f.val a).snd := rfl

def pointDerivationsCongr {x y : S →ₐ[ℂ] ℂ} (h : x = y) : pointDerivations x ≃ₗ[ℂ] pointDerivations y :=
  LinearEquiv.ofEq _ _ (congrArg pointDerivations h)

theorem pointDerivationsCongr_apply {x y : S →ₐ[ℂ] ℂ} (h : x = y)
    (D : pointDerivations x) (a : S) : (pointDerivationsCongr h D).val a = D.val a := by
  cases h
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations
