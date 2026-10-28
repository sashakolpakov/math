import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Ring Map Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RingMapBaseChange

noncomputable section

/-! Standard projective space has a canonical base-change isomorphism for every explicit coefficient ring map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def polynomialProjectiveBaseChangeIso {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ) :
    ProjectivePresentations.affineProjectiveSpace A n ≅ (Over.pullback (Spec.map φ)).obj (ProjectivePresentations.affineProjectiveSpace R n) :=
  Over.isoMk (CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n).isoPullback
    (CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n).isoPullback_hom_snd

theorem polynomialProjectiveBaseChangeIso_hom_fst {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ) :
    (polynomialProjectiveBaseChangeIso φ n).hom.left ≫
      pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom (Spec.map φ) = CoefficientFunctoriality.polynomialProjectiveMap φ n :=
  (CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n).isoPullback_hom_fst

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RingMapBaseChange
