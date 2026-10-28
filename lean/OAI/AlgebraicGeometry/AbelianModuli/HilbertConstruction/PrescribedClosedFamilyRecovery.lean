import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedRecoveryEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedClosedFamilyCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.CartesianEquality

/-! # Prescribed Closed Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The smooth model recovers the given ideal-defined family in its prescribed projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedClosedFamily_recovery
    {C K R : CommRingCat.{u}} (φ : C ⟶ K) (ψ : K ⟶ R) {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n))
    {X : Over (Spec C)} (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace C n) [IsClosedImmersion i.left]
    (L : Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel ((Over.pullback (Spec.map φ)).obj X) (Spec.map ψ))
    (q : F.scheme.left ⟶ X.left)
    (h : IsPullback q F.scheme.hom X.hom (Spec.map ψ ≫ Spec.map φ))
    (hw : q ≫ i.left = F.inclusion.left ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n) :
    F = (L.prescribedClosedFamily φ (Spec.map ψ) i).pullbackAlong
      (Projective.CoefficientFunctoriality.polynomialProjectiveMap ψ n) (Spec.map ψ) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback ψ n) := by
  let G := L.prescribedClosedFamily φ (Spec.map ψ) i
  let e : L.scheme ≅ G.scheme := L.prescribedClosedFamilyIso φ (Spec.map ψ) i
  let j : L.scheme.left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace K n).left :=
    (L.prescribedEmbedding φ (Spec.map ψ) i).left
  let qY : F.scheme.left ⟶ L.scheme.left := L.prescribedRecoveryMap φ ψ q h
  have he : e.hom.left ≫ G.inclusion.left = j :=
    congrArg (fun k => k.left) (L.prescribedClosedFamilyIso_inclusion φ (Spec.map ψ) i)
  have : IsIso e.hom.left := (Over.forget (Spec K)).map_isIso e.hom
  have hi : IsPullback e.hom.left j G.inclusion.left (𝟙 (Projective.ProjectivePresentations.affineProjectiveSpace K n).left) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id j).symm⟩
  have hq : IsPullback qY F.inclusion.left j (Projective.CoefficientFunctoriality.polynomialProjectiveMap ψ n) :=
    L.prescribedEmbedding_recovery_isPullback φ ψ F.inclusion i q h hw
  have H := hq.paste_horiz hi
  simp only [Category.comp_id] at H
  exact Closed.Families.FlatClosedFamily.eq_pullbackAlong_of_isPullback F G _ _
    (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback ψ n) (qY ≫ e.hom.left) H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
