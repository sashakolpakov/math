import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImmersionTransport

/-! # Model Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModelConjugation

noncomputable section

/-! Recovery isomorphisms transport actual affine maps to tensor-model maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A B X Y : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
variable [Algebra R A] [Algebra R B] [Algebra R X] [Algebra R Y]

def modelConjugateMap (eA : A ≃ₐ[R] X) (eB : B ≃ₐ[R] Y) (φ : A →ₐ[R] B) : X →ₐ[R] Y :=
  eB.toAlgHom.comp (φ.comp eA.symm.toAlgHom)

theorem modelConjugateMap_recovery (eA : A ≃ₐ[R] X) (eB : B ≃ₐ[R] Y) (φ : A →ₐ[R] B) (a : A) :
    modelConjugateMap eA eB φ (eA a) = eB (φ a) := by
  change eB (φ (eA.symm (eA a))) = eB (φ a)
  rw [eA.symm_apply_apply]

theorem modelConjugateMap_isOpenImmersion
    (eA : A ≃ₐ[R] X) (eB : B ≃ₐ[R] Y) (φ : A →ₐ[R] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (modelConjugateMap eA eB φ).toRingHom)) :=
  ImmersionTransport.isOpenImmersion_SpecMap_of_conjugate φ.toRingHom (modelConjugateMap eA eB φ).toRingHom
    eA.toRingEquiv eB.toRingEquiv (fun a => (modelConjugateMap_recovery eA eB φ a).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModelConjugation
