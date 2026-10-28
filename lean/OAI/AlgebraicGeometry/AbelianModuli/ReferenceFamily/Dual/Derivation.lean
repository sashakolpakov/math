import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import Mathlib.RingTheory.Derivation.Basic

/-! # Derivation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation

noncomputable section

section

/-! A map of dual-number products that reduces to the identity has an
actual derivation as its first-order coefficient. Fixing the base's
nilpotent parameter recovers the whole map from that derivation. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (f : DualNumber A →ₐ[k] DualNumber A)
    (hred : ∀ u, (f u).fst = u.fst)

def dualIdentityDerivation : Derivation k A A where
  toLinearMap := ((TrivSqZeroExt.sndHom A A).restrictScalars k).comp
    (f.toLinearMap.comp (TrivSqZeroExt.inlAlgHom k A A).toLinearMap)
  map_one_eq_zero' := by
    change (f ((TrivSqZeroExt.inlAlgHom k A A) 1)).snd = 0
    rw [map_one, map_one]
    rfl
  leibniz' a b := by
    change (f ((TrivSqZeroExt.inlAlgHom k A A) (a * b))).snd =
      a * (f ((TrivSqZeroExt.inlAlgHom k A A) b)).snd +
        b * (f ((TrivSqZeroExt.inlAlgHom k A A) a)).snd
    rw [map_mul, map_mul]
    change (f ((TrivSqZeroExt.inlAlgHom k A A) a)).fst *
        (f ((TrivSqZeroExt.inlAlgHom k A A) b)).snd +
      (f ((TrivSqZeroExt.inlAlgHom k A A) a)).snd *
        (f ((TrivSqZeroExt.inlAlgHom k A A) b)).fst = _
    rw [hred, hred]
    change a * (f ((TrivSqZeroExt.inlAlgHom k A A) b)).snd +
      (f ((TrivSqZeroExt.inlAlgHom k A A) a)).snd * b = _
    rw [mul_comm (f ((TrivSqZeroExt.inlAlgHom k A A) a)).snd b]

theorem dualIdentityDerivation_apply (a : A) :
    dualIdentityDerivation f hred a = (f (TrivSqZeroExt.inl a)).snd := rfl

theorem dualReductionIdentity_normalForm
    (heps : f DualNumber.eps = DualNumber.eps) (u : DualNumber A) :
    f u = (u.fst, dualIdentityDerivation f hred u.fst + u.snd) := by
  have hu : u = (TrivSqZeroExt.inl u.fst : DualNumber A) +
      (TrivSqZeroExt.inl u.snd : DualNumber A) * DualNumber.eps := by
    apply TrivSqZeroExt.ext <;> simp
  calc
    f u = f ((TrivSqZeroExt.inl u.fst : DualNumber A) +
      (TrivSqZeroExt.inl u.snd : DualNumber A) * DualNumber.eps) := congrArg f hu
    _ = f (TrivSqZeroExt.inl u.fst) + f (TrivSqZeroExt.inl u.snd) * DualNumber.eps := by
      rw [map_add, map_mul, heps]
    _ = (show DualNumber A from (u.fst, dualIdentityDerivation f hred u.fst + u.snd)) := by
      apply TrivSqZeroExt.ext
      · change (f (TrivSqZeroExt.inl u.fst)).fst + (f (TrivSqZeroExt.inl u.snd)).fst * 0 = u.fst
        rw [mul_zero, add_zero, hred]
        rfl
      · change (f (TrivSqZeroExt.inl u.fst)).snd +
          ((f (TrivSqZeroExt.inl u.snd)).fst * 1 + (f (TrivSqZeroExt.inl u.snd)).snd * 0) = _
        rw [mul_one, mul_zero, add_zero, hred]
        rfl

end

section

/-! Derivations construct exactly the automorphisms of a dual-number
product that fix the base parameter and reduce to the identity.
Composition is addition of the actual first-order coefficients. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

def dualDerivationAutomorphism (d : Derivation k A A) : DualNumber A ≃ₐ[k] DualNumber A where
  toFun u := (u.fst, d u.fst + u.snd)
  invFun u := (u.fst, -d u.fst + u.snd)
  left_inv u := by
    apply TrivSqZeroExt.ext
    · rfl
    · change -d u.fst + (d u.fst + u.snd) = u.snd
      abel
  right_inv u := by
    apply TrivSqZeroExt.ext
    · rfl
    · change d u.fst + (-d u.fst + u.snd) = u.snd
      abel
  map_add' u v := by
    apply TrivSqZeroExt.ext
    · rfl
    · change d (u.fst + v.fst) + (u.snd + v.snd) =
        (d u.fst + u.snd) + (d v.fst + v.snd)
      rw [map_add]
      abel
  map_mul' u v := by
    apply TrivSqZeroExt.ext
    · rfl
    · change d (u.fst * v.fst) + (u.fst * v.snd + u.snd * v.fst) =
        u.fst * (d v.fst + v.snd) + (d u.fst + u.snd) * v.fst
      rw [d.leibniz]
      simp only [smul_eq_mul]
      ring
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    · change d (algebraMap k A c) + 0 = 0
      rw [d.map_algebraMap, add_zero]

theorem dualDerivationAutomorphism_apply (d : Derivation k A A) (u : DualNumber A) :
    dualDerivationAutomorphism d u = (u.fst, d u.fst + u.snd) := rfl

theorem dualDerivationAutomorphism_reduction (d : Derivation k A A) (u : DualNumber A) :
    (dualDerivationAutomorphism d u).fst = u.fst := rfl

theorem dualDerivationAutomorphism_eps (d : Derivation k A A) :
    dualDerivationAutomorphism d DualNumber.eps = DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · rfl
  · change d 0 + 1 = 1
    rw [map_zero, zero_add]

theorem dualIdentityDerivation_of_automorphism (d : Derivation k A A) :
    dualIdentityDerivation (dualDerivationAutomorphism d).toAlgHom
      (dualDerivationAutomorphism_reduction d) = d := by
  apply Derivation.ext
  intro a
  change d a + 0 = d a
  exact add_zero _

theorem dualDerivationAutomorphism_recover (f : DualNumber A →ₐ[k] DualNumber A)
    (hred : ∀ u, (f u).fst = u.fst) (heps : f DualNumber.eps = DualNumber.eps) :
    (dualDerivationAutomorphism (dualIdentityDerivation f hred)).toAlgHom = f := by
  apply AlgHom.ext
  intro u
  exact (dualReductionIdentity_normalForm f hred heps u).symm

theorem dualDerivationAutomorphism_trans (d e : Derivation k A A) :
    (dualDerivationAutomorphism d).trans (dualDerivationAutomorphism e) =
      dualDerivationAutomorphism (d + e) := by
  apply AlgEquiv.ext
  intro u
  apply TrivSqZeroExt.ext
  · rfl
  · change e u.fst + (d u.fst + u.snd) = (d u.fst + e u.fst) + u.snd
    abel

theorem dualDerivationAutomorphism_zero :
    dualDerivationAutomorphism (0 : Derivation k A A) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro u
  apply TrivSqZeroExt.ext
  · rfl
  · change 0 + u.snd = u.snd
    exact zero_add _

end

/-! First-order transition coefficients commute with the actual algebra
restriction maps. Derivation gauges preserve the same restriction squares. -/

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

theorem dualNumberAlgMap_inl (q : A →ₐ[k] B) (a : A) :
    NumberCoefficients.dualNumberAlgMap q (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (q a) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change q 0 = 0
    exact map_zero _

theorem dualIdentityDerivation_natural (q : A →ₐ[k] B)
    (f : DualNumber A →ₐ[k] DualNumber A) (g : DualNumber B →ₐ[k] DualNumber B)
    (hf : ∀ u, (f u).fst = u.fst) (hg : ∀ u, (g u).fst = u.fst)
    (hcomm : (NumberCoefficients.dualNumberAlgMap q).comp f = g.comp (NumberCoefficients.dualNumberAlgMap q)) (a : A) :
    q (dualIdentityDerivation f hf a) = dualIdentityDerivation g hg (q a) := by
  have he := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun hcomm (TrivSqZeroExt.inl a))
  change (NumberCoefficients.dualNumberAlgMap q (f (TrivSqZeroExt.inl a))).snd =
    (g (NumberCoefficients.dualNumberAlgMap q (TrivSqZeroExt.inl a))).snd at he
  rw [dualNumberAlgMap_inl] at he
  exact he

theorem dualDerivationAutomorphism_natural (q : A →ₐ[k] B)
    (d : Derivation k A A) (e : Derivation k B B)
    (hcomm : ∀ a, q (d a) = e (q a)) :
    (NumberCoefficients.dualNumberAlgMap q).comp (dualDerivationAutomorphism d).toAlgHom =
      (dualDerivationAutomorphism e).toAlgHom.comp (NumberCoefficients.dualNumberAlgMap q) := by
  apply AlgHom.ext
  intro u
  apply TrivSqZeroExt.ext
  · rfl
  · change q (d u.fst + u.snd) = e (q u.fst) + q u.snd
    rw [map_add, hcomm]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation
