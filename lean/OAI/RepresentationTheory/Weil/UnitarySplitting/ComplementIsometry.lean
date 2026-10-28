import OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair
import OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticPlane

/-! # Complement Isometry -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ComplementIsometry.Transvections

noncomputable section

section

/-! Extending isometries of a symplectic plane complement, and restricting
isometries which fix the plane. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair.Construction OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticPlane

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
variable (u v : V) (huv : B u v = 1)

include hAlt in
theorem complement_alternating : (B.restrict (SymplecticPlane.planeComplement B u v)).IsAlt :=
  fun x => hAlt x.val

def planeExtension :
    DualPair.Construction.pairingIsometries (fun x y => (B.restrict (SymplecticPlane.planeComplement B u v)) x y) →*
      DualPair.Construction.pairingIsometries (fun x y => B x y) where
  toFun g := ⟨((SymplecticPlane.decomposePlane B hAlt u v huv).trans
    ((LinearEquiv.refl F (F × F)).prodCongr g.val)).trans (SymplecticPlane.decomposePlane B hAlt u v huv).symm, by
      intro x y
      let e := SymplecticPlane.decomposePlane B hAlt u v huv
      change B (e.symm ((e x).1, g.val (e x).2)) (e.symm ((e y).1, g.val (e y).2)) = B x y
      rw [SymplecticPlane.pairing_decomposition]
      have hp := SymplecticPlane.pairing_decomposition B hAlt u v huv (e x) (e y)
      change B (e.symm (e x)) (e.symm (e y)) = _ at hp
      rw [e.symm_apply_apply, e.symm_apply_apply] at hp
      have hg := g.property (e x).2 (e y).2
      change B (g.val (e x).2).val (g.val (e y).2).val = B (e x).2.val (e y).2.val at hg
      dsimp only at hg ⊢
      rw [hg]
      exact hp.symm⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (SymplecticPlane.decomposePlane B hAlt u v huv).symm_apply_apply x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    let e := SymplecticPlane.decomposePlane B hAlt u v huv
    change e.symm ((e x).1, g.val (h.val (e x).2)) =
      e.symm ((e (e.symm ((e x).1, h.val (e x).2))).1,
        g.val (e (e.symm ((e x).1, h.val (e x).2))).2)
    rw [e.apply_symm_apply]

theorem planeExtension_apply
    (g : DualPair.Construction.pairingIsometries (fun x y => (B.restrict (SymplecticPlane.planeComplement B u v)) x y)) (x : V) :
    (planeExtension B hAlt u v huv g).val x =
      (-B v x) • u + B u x • v + (g.val (SymplecticPlane.remainderToComplement B hAlt u v huv x)).val := rfl

theorem planeExtension_transvection (w : SymplecticPlane.planeComplement B u v) (a : F) :
    planeExtension B hAlt u v huv
      (DualPair.Transvections.transvection (B.restrict (SymplecticPlane.planeComplement B u v)) (complement_alternating B hAlt u v) w a) =
        DualPair.Transvections.transvection B hAlt w.val a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [planeExtension_apply, DualPair.Transvections.transvection_apply, DualPair.Transvections.transvection_apply]
  change (-B v x) • u + B u x • v +
    ((SymplecticPlane.remainderToComplement B hAlt u v huv x).val +
      (a * B w.val (SymplecticPlane.remainderToComplement B hAlt u v huv x).val) • w.val) =
        x + (a * B w.val x) • w.val
  have hwu : B w.val u = 0 := hAlt.eq_iff.mp w.property.1
  have hwv : B w.val v = 0 := hAlt.eq_iff.mp w.property.2
  change (-B v x) • u + B u x • v +
    (SymplecticPlane.planeRemainder B u v x + (a * B w.val (SymplecticPlane.planeRemainder B u v x)) • w.val) = _
  rw [SymplecticPlane.planeRemainder_apply]
  simp only [map_sub, map_add, map_smul, hwu, hwv, smul_eq_mul, mul_zero, add_zero, sub_zero]
  module

theorem planeExtension_mem
    (g : DualPair.Construction.pairingIsometries (fun x y => (B.restrict (SymplecticPlane.planeComplement B u v)) x y))
    (hg : g ∈ DualPair.Transvections.transvectionSubgroup (B.restrict (SymplecticPlane.planeComplement B u v)) (complement_alternating B hAlt u v)) :
    planeExtension B hAlt u v huv g ∈ DualPair.Transvections.transvectionSubgroup B hAlt := by
  have hle : DualPair.Transvections.transvectionSubgroup (B.restrict (SymplecticPlane.planeComplement B u v)) (complement_alternating B hAlt u v) ≤
      (DualPair.Transvections.transvectionSubgroup B hAlt).comap (planeExtension B hAlt u v huv) := by
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨⟨w, a⟩, rfl⟩
    change planeExtension B hAlt u v huv
      (DualPair.Transvections.transvection (B.restrict (SymplecticPlane.planeComplement B u v)) (complement_alternating B hAlt u v) w a) ∈
        DualPair.Transvections.transvectionSubgroup B hAlt
    rw [planeExtension_transvection]
    exact DualPair.Transvections.transvection_mem B hAlt w.val a
  exact hle hg

theorem fixedPlane_preserves_complement
    (g : DualPair.Construction.pairingIsometries (fun x y => B x y)) (hgu : g.val u = u) (hgv : g.val v = v)
    (x : SymplecticPlane.planeComplement B u v) : g.val x.val ∈ SymplecticPlane.planeComplement B u v := by
  constructor
  · change B u (g.val x.val) = 0
    have hh := g.property u x.val
    rw [hgu] at hh
    exact hh.trans x.property.1
  · change B v (g.val x.val) = 0
    have hh := g.property v x.val
    rw [hgv] at hh
    exact hh.trans x.property.2

def complementRestriction
    (g : DualPair.Construction.pairingIsometries (fun x y => B x y)) (hgu : g.val u = u) (hgv : g.val v = v) :
    DualPair.Construction.pairingIsometries (fun x y => (B.restrict (SymplecticPlane.planeComplement B u v)) x y) := by
  have higu : g.val.symm u = u := by
    apply g.val.injective
    rw [g.val.apply_symm_apply, hgu]
  have higv : g.val.symm v = v := by
    apply g.val.injective
    rw [g.val.apply_symm_apply, hgv]
  refine ⟨{
    toFun := fun x => ⟨g.val x.val, fixedPlane_preserves_complement B u v g hgu hgv x⟩
    invFun := fun x => ⟨g.val.symm x.val, fixedPlane_preserves_complement B u v g⁻¹ higu higv x⟩
    left_inv := fun x => Subtype.ext (g.val.symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext (g.val.apply_symm_apply x.val)
    map_add' := fun x y => Subtype.ext (g.val.map_add x.val y.val)
    map_smul' := fun a x => Subtype.ext (g.val.map_smul a x.val) }, ?_⟩
  intro x y
  exact g.property x.val y.val

theorem planeExtension_complementRestriction
    (g : DualPair.Construction.pairingIsometries (fun x y => B x y)) (hgu : g.val u = u) (hgv : g.val v = v) :
    planeExtension B hAlt u v huv (complementRestriction B u v g hgu hgv) = g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [planeExtension_apply]
  change (-B v x) • u + B u x • v + g.val (SymplecticPlane.planeRemainder B u v x) = g.val x
  rw [SymplecticPlane.planeRemainder_apply, map_sub, map_add, map_smul, map_smul, hgu, hgv]
  module

end

/-! A finite-dimensional symplectic isometry is a product of transvections.
The proof fixes a symplectic pair and inducts on its complement. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair.Construction OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticPlane

variable {F V : Type} [Field F] [CharZero F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V]

theorem mem_transvectionSubgroup
    (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt) (hND : B.Nondegenerate)
    (g : DualPair.Construction.pairingIsometries (fun x y => B x y)) : g ∈ DualPair.Transvections.transvectionSubgroup B hAlt := by
  suffices ∀ N : ℕ, Module.finrank F V = N → g ∈ DualPair.Transvections.transvectionSubgroup B hAlt from this _ rfl
  intro N hdim
  induction N using Nat.strong_induction_on generalizing V with
  | h N ih =>
    by_cases hsub : Subsingleton V
    · let : Subsingleton V := hsub
      have hg : g = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        exact Subsingleton.elim _ _
      rw [hg]
      exact (DualPair.Transvections.transvectionSubgroup B hAlt).one_mem
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨u, hu⟩ := exists_ne (0 : V)
      obtain ⟨v₀, hv₀⟩ : ∃ v₀, B u v₀ ≠ 0 := by
        by_contra! hh
        exact hu (hND.1 u hh)
      let v := (B u v₀)⁻¹ • v₀
      have huv : B u v = 1 := by simp [v, hv₀]
      have hgu0 : g.val u ≠ 0 := by
        intro hh
        apply hu
        apply g.val.injective
        rw [map_zero]
        exact hh
      obtain ⟨t, ht, htu⟩ := DualPair.Transvections.exists_transvection_word_sends B hAlt hND (g.val u) u hgu0 hu
      let g₁ := t * g
      have h₁u : g₁.val u = u := htu
      have hpair : B u (g₁.val v) = 1 := by
        have hh : B (g₁.val u) (g₁.val v) = B u v := g₁.property u v
        rw [h₁u, huv] at hh
        exact hh
      obtain ⟨s, hs, hsu, hsv⟩ := DualPair.Transvections.exists_transvection_word_fixes_sends B hAlt u (g₁.val v) v hpair huv
      let g₂ := s * g₁
      have h₂u : g₂.val u = u := by
        change s.val (g₁.val u) = u
        rw [h₁u, hsu]
      have h₂v : g₂.val v = v := hsv
      let W := SymplecticPlane.planeComplement B u v
      have hdimW : Module.finrank F W < N := by
        have heq := (SymplecticPlane.decomposePlane B hAlt u v huv).finrank_eq
        simp only [Module.finrank_prod, Module.finrank_self] at heq
        change Module.finrank F V = (1 + 1) + Module.finrank F W at heq
        omega
      have hAltW : (B.restrict W).IsAlt := fun x => hAlt x.val
      have hNDW : (B.restrict W).Nondegenerate := SymplecticPlane.complement_nondegenerate B hAlt hND u v huv
      let k := complementRestriction B u v g₂ h₂u h₂v
      have hk : k ∈ DualPair.Transvections.transvectionSubgroup (B.restrict W) hAltW :=
        ih (Module.finrank F W) hdimW (B.restrict W) hAltW hNDW k rfl
      have hg₂ : g₂ ∈ DualPair.Transvections.transvectionSubgroup B hAlt := by
        have hh := planeExtension_mem B hAlt u v huv k hk
        rw [planeExtension_complementRestriction] at hh
        exact hh
      have hword : t⁻¹ * s⁻¹ * g₂ ∈ DualPair.Transvections.transvectionSubgroup B hAlt :=
        (DualPair.Transvections.transvectionSubgroup B hAlt).mul_mem
          ((DualPair.Transvections.transvectionSubgroup B hAlt).mul_mem
            ((DualPair.Transvections.transvectionSubgroup B hAlt).inv_mem ht) ((DualPair.Transvections.transvectionSubgroup B hAlt).inv_mem hs)) hg₂
      convert hword using 1
      dsimp [g₂, g₁]
      group

theorem transvectionSubgroup_eq_top
    (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt) (hND : B.Nondegenerate) :
    DualPair.Transvections.transvectionSubgroup B hAlt = ⊤ := by
  apply top_unique
  intro g _
  exact mem_transvectionSubgroup B hAlt hND g

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ComplementIsometry.Transvections
