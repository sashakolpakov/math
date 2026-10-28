import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedModelRecoveryMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredRecoveryNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FactoredRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison

/-! # Prescribed Recovery Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The lifted recovery preserves the prescribed projective embedding and gives its Cartesian recovery square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {C K R : CommRingCat.{u}} (φ : C ⟶ K) (ψ : K ⟶ R)
variable {A : Over (Spec R)} {X : Over (Spec C)} {n : ℕ}
variable (f : A ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace C n)
variable (L : Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel ((Over.pullback (Spec.map φ)).obj X) (Spec.map ψ))
variable (q : A.left ⟶ X.left) (h : IsPullback q A.hom X.hom (Spec.map ψ ≫ Spec.map φ))
variable (hw : q ≫ i.left = f.left ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n)

include hw

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedRecoveryMap_embedding :
    L.prescribedRecoveryMap φ ψ q h ≫ (L.prescribedEmbedding φ (Spec.map ψ) i).left =
      f.left ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap ψ n := by
  let c := Spec.map φ
  let r := Spec.map ψ
  let a : A.left ⟶ pullback X.hom c := FactoredBaseRecovery.factoredBaseRecovery q A.hom X.hom r c h
  let b : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶ pullback (Projective.ProjectivePresentations.affineProjectiveSpace C n).hom c :=
    FactoredBaseRecovery.factoredBaseRecovery _ _ _ _ _ (Projective.FactoredRecovery.polynomialProjectiveComposite_isPullback φ ψ n)
  let g : pullback X.hom c ⟶ pullback (Projective.ProjectivePresentations.affineProjectiveSpace C n).hom c := ((Over.pullback c).map i).left
  let u : L.scheme.left ⟶ pullback X.hom c := L.embedding.left
  let e : (Projective.ProjectivePresentations.affineProjectiveSpace K n).left ⟶ pullback (Projective.ProjectivePresentations.affineProjectiveSpace C n).hom c :=
    (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).hom.left
  let d : pullback (Projective.ProjectivePresentations.affineProjectiveSpace C n).hom c ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace K n).left :=
    (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).inv.left
  let f₀ : A.left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left := f.left
  let p₀ : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace K n).left := Projective.CoefficientFunctoriality.polynomialProjectiveMap ψ n
  let qY : A.left ⟶ L.scheme.left := L.prescribedRecoveryMap φ ψ q h
  have hq : qY ≫ u = a := L.prescribedRecoveryMap_comp_model φ ψ q h
  have hn : a ≫ g = f₀ ≫ b := FactoredRecoveryNaturality.factoredBaseRecovery_natural r c f i q
    (Projective.CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n) h (Projective.FactoredRecovery.polynomialProjectiveComposite_isPullback φ ψ n) hw
  have hp : b = p₀ ≫ e := Projective.FactoredRecovery.polynomialProjective_factoredRecovery φ ψ n
  have he : e ≫ d = 𝟙 (Projective.ProjectivePresentations.affineProjectiveSpace K n).left :=
    congrArg (fun k => k.left) (Projective.RingMapBaseChange.polynomialProjectiveBaseChangeIso φ n).hom_inv_id
  change qY ≫ (u ≫ g ≫ d) = f₀ ≫ p₀
  rw [← Category.assoc, hq, ← Category.assoc, hn, hp]
  simp only [Category.assoc, he, Category.comp_id]

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedEmbedding_recovery_isPullback :
    IsPullback (L.prescribedRecoveryMap φ ψ q h) f.left
      (L.prescribedEmbedding φ (Spec.map ψ) i).left (Projective.CoefficientFunctoriality.polynomialProjectiveMap ψ n) :=
  Cartesian.DiagramComparison.isPullback_arrow_of_base_squares _ _ A.hom (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom
    L.scheme.hom (Projective.ProjectivePresentations.affineProjectiveSpace K n).hom (Spec.map ψ) _ _
    (L.prescribedRecoveryMap_isPullback φ ψ q h) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback ψ n)
    f.w (L.prescribedEmbedding φ (Spec.map ψ) i).w (L.prescribedRecoveryMap_embedding φ ψ f i q h hw)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
