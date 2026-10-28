import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Fractions -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions

noncomputable section

/-! Partial fractions retain the normal Koszul variables and divide
only by the point parameters. These are the actual components of the
mixed Koszul-to-supported-Čech comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DenominatorUnits
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)

abbrev rings := P ⋙ forget₂ (CommAlgCat R) CommRingCat
abbrev modules := P ⋙ forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

def scalars : (Functor.const Cᵒᵖ).obj (CommRingCat.of R) ⟶ rings R P where
  app a := CommRingCat.ofHom (algebraMap R (P.obj a))
  naturality a b f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact ((P.map f).hom.commutes r).symm

variable {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (t : Fin m → R) (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

abbrev normal := Fin c → R
abbrev parameters := Fin m → R
abbrev ambient := (Fin c → R) × (Fin m → R)

def tuple {q : ℕ} (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) : Fin q → ambient R (c := c) (m := m) :=
  fun j => (0, Pi.basisFun R (Fin m) (a.val j).down)

def insertion (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    (⋀[R]^p (normal R (c := c))) →ₗ[R] (⋀[R]^(p + q) (ambient R (c := c) (m := m))) :=
  (Koszul.OrderedProduct.rightWord R _ p q (tuple R (c := c) a)).comp
    (exteriorPower.map p (LinearMap.inl R (normal R (c := c)) (parameters R (m := m))))

def reciprocal {q : ℕ} (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) : P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)) :=
  ((Cech.DenominatorUnits.denominator U (rings R P) R (scalars R P) (fun i => t i.down) ht a)⁻¹).val

def coordinate (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    Module.Dual R (⋀[R]^(p + q) (ambient R (c := c) (m := m))) →ₗ[R]
      ((⋀[R]^p (normal R (c := c))) →ₗ[R] P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a))) where
  toFun φ :=
    reciprocal R P U t ht a •
      ((Algebra.linearMap R (P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))).comp
        (φ.comp (insertion R p q a)))
  map_add' φ ψ := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply, map_add, smul_add]
  map_smul' r φ := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply, map_smul]
    exact smul_comm _ _ _

theorem coordinate_apply (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q)
    (φ : Module.Dual R (⋀[R]^(p + q) (ambient R (c := c) (m := m))))
    (x : ⋀[R]^p (normal R (c := c))) :
    coordinate R P U t ht p q a φ x =
      reciprocal R P U t ht a *
        algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a))) (φ (insertion R p q a x)) := rfl

theorem coordinate_zero (p : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) 0)
    (φ : Module.Dual R (⋀[R]^p (ambient R (c := c) (m := m))))
    (x : ⋀[R]^p (normal R (c := c))) :
    coordinate R P U t ht p 0 a φ x =
      algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U 0).obj a)))
        (φ (exteriorPower.map p (LinearMap.inl R (normal R (c := c)) (parameters R (m := m))) x)) := by
  have hi : insertion R p 0 a x =
      exteriorPower.map p (LinearMap.inl R (normal R (c := c)) (parameters R (m := m))) x := by
    apply Subtype.ext
    change _ * ExteriorAlgebra.ιMulti R 0 _ = _
    rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  rw [coordinate_apply, hi]
  simp [reciprocal, Cech.DenominatorUnits.denominator]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions
