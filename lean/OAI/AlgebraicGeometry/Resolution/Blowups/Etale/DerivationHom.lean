import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation
import Mathlib.RingTheory.RingHom.Etale

/-! # Derivation Hom -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom.Construction

noncomputable section

/-! Extend relative derivations through explicit coefficient-preserving étale ring maps. -/

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- This explicit-map form fixes the coefficient algebra without requiring
the caller to replace any preexisting scalar action on a blowup chart. -/
def extendEtaleRingDerivationHom (φ : R →+* S) (hφ : φ.Etale)
    (hk : ∀ x : k, φ (algebraMap k R x) = algebraMap k S x) (D : Derivation k R R) :
    Derivation k S S := by
  let : Algebra R S := φ.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (hk x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hφ
  exact Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D

theorem extendEtaleRingDerivationHom_apply (φ : R →+* S) (hφ : φ.Etale)
    (hk : ∀ x : k, φ (algebraMap k R x) = algebraMap k S x) (D : Derivation k R R) (r : R) :
    extendEtaleRingDerivationHom k φ hφ hk D (φ r) = φ (D r) := by
  let : Algebra R S := φ.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (hk x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hφ
  exact Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (S := S) D r

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom.Construction
