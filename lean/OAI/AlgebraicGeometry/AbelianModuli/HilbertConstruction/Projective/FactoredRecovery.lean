import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RingMapBaseChange

/-! # Factored Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FactoredRecovery

noncomputable section

/-! Factored recovery of standard projective space is the usual projective coefficient map followed by the canonical pullback presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem polynomialProjectiveComposite_isPullback {C K R : CommRingCat.{u}}
    (φ : C ⟶ K) (ψ : K ⟶ R) (n : ℕ) :
    IsPullback (CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n) (ProjectivePresentations.affineProjectiveSpace R n).hom
      (ProjectivePresentations.affineProjectiveSpace C n).hom (Spec.map ψ ≫ Spec.map φ) :=
  (congrArg (fun c => IsPullback (CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n) (ProjectivePresentations.affineProjectiveSpace R n).hom
    (ProjectivePresentations.affineProjectiveSpace C n).hom c) (Spec.map_comp φ ψ)).mp (CoefficientFunctoriality.polynomialProjectiveMap_isPullback (φ ≫ ψ) n)

theorem polynomialProjective_factoredRecovery {C K R : CommRingCat.{u}}
    (φ : C ⟶ K) (ψ : K ⟶ R) (n : ℕ) :
    FactoredBaseRecovery.factoredBaseRecovery (CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n) (ProjectivePresentations.affineProjectiveSpace R n).hom
      (ProjectivePresentations.affineProjectiveSpace C n).hom (Spec.map ψ) (Spec.map φ)
      (polynomialProjectiveComposite_isPullback φ ψ n) =
        CoefficientFunctoriality.polynomialProjectiveMap ψ n ≫ (RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).hom.left := by
  let q : (ProjectivePresentations.affineProjectiveSpace R n).left ⟶
      pullback (ProjectivePresentations.affineProjectiveSpace C n).hom (Spec.map φ) :=
    FactoredBaseRecovery.factoredBaseRecovery _ _ _ _ _ (polynomialProjectiveComposite_isPullback φ ψ n)
  let p : (ProjectivePresentations.affineProjectiveSpace R n).left ⟶ (ProjectivePresentations.affineProjectiveSpace K n).left := CoefficientFunctoriality.polynomialProjectiveMap ψ n
  let e : (ProjectivePresentations.affineProjectiveSpace K n).left ⟶ pullback (ProjectivePresentations.affineProjectiveSpace C n).hom (Spec.map φ) :=
    (RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).hom.left
  have he₁ : e ≫ pullback.fst (ProjectivePresentations.affineProjectiveSpace C n).hom (Spec.map φ) = CoefficientFunctoriality.polynomialProjectiveMap φ n :=
    RingMapBaseChange.polynomialProjectiveBaseChangeIso_hom_fst φ n
  have he₂ : e ≫ pullback.snd (ProjectivePresentations.affineProjectiveSpace C n).hom (Spec.map φ) = (ProjectivePresentations.affineProjectiveSpace K n).hom :=
    (RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).hom.w
  change q = p ≫ e
  apply pullback.hom_ext
  · rw [FactoredBaseRecovery.factoredBaseRecovery_fst, Category.assoc, he₁]
    exact CoefficientFunctoriality.polynomialProjectiveMap_comp φ ψ n
  · rw [FactoredBaseRecovery.factoredBaseRecovery_snd, Category.assoc, he₂]
    exact (CoefficientFunctoriality.polynomialProjectiveMap_over ψ n).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FactoredRecovery
