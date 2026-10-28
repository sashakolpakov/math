import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site
import Mathlib.Algebra.Algebra.Equiv

/-! # Isomorphisms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Isomorphisms.CrystallineIsomorphisms

noncomputable section

/-!
# Isomorphisms of native crystalline objects

Bijective ambient and residual algebra maps have an inverse in the
actual crystalline category. The inverse preserves the reduction,
the immersion in the special fibre, and the full divided powers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {P Q : Site.Object p k X}
  (f : P ⟶ Q) (ha : Function.Bijective f.ambientMap) (hr : Function.Bijective f.reducedMap)

def ambientInverse : P.thickening.ring →ₐ[WittVector p k] Q.thickening.ring :=
  (AlgEquiv.ofBijective f.ambientMap ha).symm.toAlgHom

def reducedInverse : P.residueRing →ₐ[k] Q.residueRing :=
  (AlgEquiv.ofBijective f.reducedMap hr).symm.toAlgHom

theorem inverse_reduction (x : P.thickening.ring) :
    Q.thickening.reduction (ambientInverse p k X f ha x) =
      reducedInverse p k X f hr (P.thickening.reduction x) := by
  apply hr.injective
  rw [← f.reduction_comm]
  change P.thickening.reduction (f.ambientMap ((AlgEquiv.ofBijective f.ambientMap ha).symm x)) =
    f.reducedMap ((AlgEquiv.ofBijective f.reducedMap hr).symm (P.thickening.reduction x))
  rw [AlgEquiv.ofBijective_apply_symm_apply, AlgEquiv.ofBijective_apply_symm_apply]

include hr in
theorem inverse_isDPMorphism :
    DividedPowers.IsDPMorphism P.thickening.dividedPowers Q.thickening.dividedPowers
      (ambientInverse p k X f ha).toRingHom where
  ideal_comp := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change Q.thickening.reduction (ambientInverse p k X f ha x) = 0
    rw [inverse_reduction p k X f ha hr, show P.thickening.reduction x = 0 from hx, map_zero]
  dpow_comp {n} x hx := by
    have hi : ambientInverse p k X f ha x ∈ RingHom.ker Q.thickening.reduction := by
      change Q.thickening.reduction (ambientInverse p k X f ha x) = 0
      rw [inverse_reduction p k X f ha hr, show P.thickening.reduction x = 0 from hx, map_zero]
    apply ha.injective
    exact (f.dp_comp.dpow_comp _ hi).symm.trans
      ((congrArg (P.thickening.dividedPowers.dpow n)
        (AlgEquiv.ofBijective_apply_symm_apply f.ambientMap ha x)).trans
          (AlgEquiv.ofBijective_apply_symm_apply f.ambientMap ha (P.thickening.dividedPowers.dpow n x)).symm)

def inverse : Q ⟶ P where
  ambientMap := ambientInverse p k X f ha
  reducedMap := reducedInverse p k X f hr
  reduction_comm := inverse_reduction p k X f ha hr
  over_X := by
    rw [← f.over_X, ← Category.assoc, ← Spec.map_comp]
    have he : (reducedInverse p k X f hr).toRingHom.comp f.reducedMap.toRingHom = RingHom.id Q.residueRing := by
      ext x
      exact AlgEquiv.ofBijective_symm_apply_apply f.reducedMap hr x
    change Spec.map (CommRingCat.ofHom ((reducedInverse p k X f hr).toRingHom.comp f.reducedMap.toRingHom)) ≫ Q.immersion = Q.immersion
    rw [he]
    change Spec.map (𝟙 Q.residueRing) ≫ Q.immersion = Q.immersion
    rw [Spec.map_id, Category.id_comp]
  dp_comp := inverse_isDPMorphism p k X f ha hr

def iso : P ≅ Q where
  hom := f
  inv := inverse p k X f ha hr
  hom_inv_id := by
    apply Site.Object.Hom.ext
    · ext x
      exact AlgEquiv.ofBijective_apply_symm_apply f.reducedMap hr x
    · ext x
      exact AlgEquiv.ofBijective_apply_symm_apply f.ambientMap ha x
  inv_hom_id := by
    apply Site.Object.Hom.ext
    · ext x
      exact AlgEquiv.ofBijective_symm_apply_apply f.reducedMap hr x
    · ext x
      exact AlgEquiv.ofBijective_symm_apply_apply f.ambientMap ha x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Isomorphisms.CrystallineIsomorphisms
