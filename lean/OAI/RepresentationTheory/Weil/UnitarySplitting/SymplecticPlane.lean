import Mathlib

/-! # Symplectic Plane -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticPlane

noncomputable section

/-! Splitting off a symplectic plane from a nondegenerate alternating
bilinear space. These are algebraic realization lemmas for UnitarySplitting. -/

open LinearMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def planeComplement (B : LinearMap.BilinForm F V) (u v : V) : Submodule F V :=
  LinearMap.ker (B u) ⊓ LinearMap.ker (B v)

theorem reversed_pair (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (u v : V) (huv : B u v = 1) : B v u = -1 := by
  rw [← hAlt.neg_eq u v, huv]

def planeRemainder (B : LinearMap.BilinForm F V) (u v : V) : V →ₗ[F] V :=
  LinearMap.id + (LinearMap.toSpanSingleton F V u).comp (B v) -
    (LinearMap.toSpanSingleton F V v).comp (B u)

theorem planeRemainder_apply (B : LinearMap.BilinForm F V) (u v x : V) :
    planeRemainder B u v x = x + B v x • u - B u x • v := rfl

theorem planeRemainder_mem (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (u v : V) (huv : B u v = 1) (x : V) :
    planeRemainder B u v x ∈ planeComplement B u v := by
  constructor
  · change B u (x + B v x • u - B u x • v) = 0
    simp [hAlt.self_eq_zero u, huv]
  · change B v (x + B v x • u - B u x • v) = 0
    simp [hAlt.self_eq_zero v, reversed_pair B hAlt u v huv]

def remainderToComplement (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (u v : V) (huv : B u v = 1) : V →ₗ[F] planeComplement B u v :=
  (planeRemainder B u v).codRestrict _ (planeRemainder_mem B hAlt u v huv)

/-- Coordinates (q,p,w), with x = p u + q v + w. -/
def decomposePlane (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (u v : V) (huv : B u v = 1) :
    V ≃ₗ[F] ((F × F) × planeComplement B u v) where
  toFun x := ((B u x, -B v x), remainderToComplement B hAlt u v huv x)
  invFun x := x.1.2 • u + x.1.1 • v + x.2.val
  left_inv x := by
    change -B v x • u + B u x • v + (x + B v x • u - B u x • v) = x
    module
  right_inv x := by
    rcases x with ⟨⟨q, p⟩, w⟩
    have huw : B u w.val = 0 := w.property.1
    have hvw : B v w.val = 0 := w.property.2
    apply Prod.ext
    · apply Prod.ext
      · change B u (p • u + q • v + w.val) = q
        simp [hAlt.self_eq_zero u, huv, huw]
      · change -B v (p • u + q • v + w.val) = p
        simp [hAlt.self_eq_zero v, reversed_pair B hAlt u v huv, hvw]
    · apply Subtype.ext
      change planeRemainder B u v (p • u + q • v + w.val) = w.val
      rw [planeRemainder_apply]
      simp only [map_add, map_smul, hAlt.self_eq_zero u, hAlt.self_eq_zero v,
        huv, reversed_pair B hAlt u v huv, huw, hvw, smul_eq_mul,
        mul_zero, zero_add, add_zero, mul_one, mul_neg, neg_smul]
      module
  map_add' x y := by
    apply Prod.ext
    · simp only [map_add, neg_add, Prod.mk_add_mk]
    · exact (remainderToComplement B hAlt u v huv).map_add x y
  map_smul' a x := by
    apply Prod.ext
    · simp only [map_smul, smul_neg, Prod.smul_mk, RingHom.id_apply]
    · exact (remainderToComplement B hAlt u v huv).map_smul a x

theorem pairing_decomposition (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (u v : V) (huv : B u v = 1)
    (a b : (F × F) × planeComplement B u v) :
    B ((decomposePlane B hAlt u v huv).symm a)
        ((decomposePlane B hAlt u v huv).symm b) =
      (a.1.2 * b.1.1 - a.1.1 * b.1.2) + B a.2.val b.2.val := by
  have hua : B u a.2.val = 0 := a.2.property.1
  have hva : B v a.2.val = 0 := a.2.property.2
  have hub : B u b.2.val = 0 := b.2.property.1
  have hvb : B v b.2.val = 0 := b.2.property.2
  have hau : B a.2.val u = 0 := hAlt.eq_iff.mp hua
  have hav : B a.2.val v = 0 := hAlt.eq_iff.mp hva
  change B (a.1.2 • u + a.1.1 • v + a.2.val)
      (b.1.2 • u + b.1.1 • v + b.2.val) = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hAlt.self_eq_zero u, hAlt.self_eq_zero v, huv,
    reversed_pair B hAlt u v huv, hub, hvb, hau, hav, smul_eq_mul]
  ring

theorem complement_nondegenerate (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (hNondeg : B.Nondegenerate) (u v : V) (huv : B u v = 1) :
    (B.restrict (planeComplement B u v)).Nondegenerate := by
  have hleft : ∀ x : planeComplement B u v,
      (∀ y : planeComplement B u v, B x.val y.val = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply hNondeg.1
    intro y
    obtain ⟨z, rfl⟩ := (decomposePlane B hAlt u v huv).symm.surjective y
    have hxu : B x.val u = 0 := hAlt.eq_iff.mp x.property.1
    have hxv : B x.val v = 0 := hAlt.eq_iff.mp x.property.2
    change B x.val (z.1.2 • u + z.1.1 • v + z.2.val) = 0
    simp [hxu, hxv, hx z.2]
  constructor
  · exact hleft
  · intro x hx
    apply hleft x
    intro y
    exact hAlt.eq_iff.mp (hx y)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticPlane
