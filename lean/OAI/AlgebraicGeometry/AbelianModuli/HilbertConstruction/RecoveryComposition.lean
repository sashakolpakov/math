import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModelConjugation

/-! # Recovery Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryComposition

noncomputable section

/-! Recovery compatibility composes through two algebra isomorphisms. -/

universe u

theorem twoStageRecovery_map
    {R A B X₀ Y₀ X₁ Y₁ X₂ Y₂ : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [CommRing X₀] [CommRing Y₀] [CommRing X₁] [CommRing Y₁] [CommRing X₂] [CommRing Y₂]
    [Algebra R A] [Algebra R B] [Algebra R X₀] [Algebra R Y₀]
    [Algebra R X₁] [Algebra R Y₁] [Algebra R X₂] [Algebra R Y₂]
    (eA : A ≃ₐ[R] X₀) (eB : B ≃ₐ[R] Y₀)
    (cA : X₁ ≃ₐ[R] X₀) (cB : Y₁ ≃ₐ[R] Y₀)
    (dA : X₂ ≃ₐ[R] X₁) (dB : Y₂ ≃ₐ[R] Y₁)
    (φ : A →ₐ[R] B) (p : X₁ →ₐ[R] Y₁) (q : X₂ →ₐ[R] Y₂)
    (hc : ∀ x, cB (p x) = Affine.ModelConjugation.modelConjugateMap eA eB φ (cA x))
    (hd : ∀ x, dB (q x) = p (dA x)) (a : A) :
    ((eB.trans cB.symm).trans dB.symm) (φ a) =
      q (((eA.trans cA.symm).trans dA.symm) a) := by
  apply dB.injective
  change dB (dB.symm (cB.symm (eB (φ a)))) = dB (q (dA.symm (cA.symm (eA a))))
  rw [dB.apply_symm_apply, hd, dA.apply_symm_apply]
  apply cB.injective
  rw [cB.apply_symm_apply, hc, cA.apply_symm_apply, Affine.ModelConjugation.modelConjugateMap_recovery]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryComposition
