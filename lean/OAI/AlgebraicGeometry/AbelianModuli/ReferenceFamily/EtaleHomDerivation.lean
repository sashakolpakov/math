import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleTransitionDerivation
import Mathlib.RingTheory.RingHom.Etale

/-! # Etale Hom Derivation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation

noncomputable section

section

/-! Derivation restriction along a specified etale algebra map keeps
the original coefficient algebra structures and the literal map. -/

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

def etaleAlgHomDerivationLinear (q : A →ₐ[k] B) (hq : q.toRingHom.Etale) :
    Derivation k A A →ₗ[k] Derivation k B B := by
  let : Algebra A B := q.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq (fun c => (q.commutes c).symm)
  have : Algebra.Etale A B := hq
  exact EtaleTransitionDerivation.etaleTransitionDerivationLinear

theorem etaleAlgHomDerivationLinear_map (q : A →ₐ[k] B) (hq : q.toRingHom.Etale)
    (d : Derivation k A A) (a : A) :
    etaleAlgHomDerivationLinear q hq d (q a) = q (d a) := by
  let : Algebra A B := q.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq (fun c => (q.commutes c).symm)
  have : Algebra.Etale A B := hq
  exact EtaleTransitionDerivation.etaleTransitionDerivation_algebraMap d a

theorem etaleAlgHomDerivationLinear_unique (q : A →ₐ[k] B) (hq : q.toRingHom.Etale)
    (d : Derivation k A A) (e : Derivation k B B) (h : ∀ a, e (q a) = q (d a)) :
    e = etaleAlgHomDerivationLinear q hq d := by
  let : Algebra A B := q.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq (fun c => (q.commutes c).symm)
  have : Algebra.Etale A B := hq
  exact EtaleTransitionDerivation.etaleTransitionDerivation_unique d e h

end

/-! Etale derivation restriction respects identities and composition. -/

variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]

theorem etaleAlgHomDerivationLinear_id (h : (AlgHom.id k A).toRingHom.Etale) :
    etaleAlgHomDerivationLinear (AlgHom.id k A) h = LinearMap.id := by
  apply LinearMap.ext
  intro d
  exact (etaleAlgHomDerivationLinear_unique (AlgHom.id k A) h d d (fun _ => rfl)).symm

theorem etaleAlgHomDerivationLinear_comp (q : A →ₐ[k] B) (r : B →ₐ[k] C)
    (hq : q.toRingHom.Etale) (hr : r.toRingHom.Etale) (hrq : (r.comp q).toRingHom.Etale) :
    etaleAlgHomDerivationLinear (r.comp q) hrq =
      (etaleAlgHomDerivationLinear r hr).comp (etaleAlgHomDerivationLinear q hq) := by
  apply LinearMap.ext
  intro d
  apply Eq.symm
  apply etaleAlgHomDerivationLinear_unique (r.comp q) hrq
  intro a
  change etaleAlgHomDerivationLinear r hr (etaleAlgHomDerivationLinear q hq d) (r (q a)) = r (q (d a))
  rw [etaleAlgHomDerivationLinear_map, etaleAlgHomDerivationLinear_map]

theorem etaleAlgHomDerivationLinear_congr (q r : A →ₐ[k] B)
    (hq : q.toRingHom.Etale) (hr : r.toRingHom.Etale) (h : q = r) :
    etaleAlgHomDerivationLinear q hq = etaleAlgHomDerivationLinear r hr := by
  subst r
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation
