import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.CoordinateBaseChange

/-! # Family Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual coefficient pullbacks of projective closed families compose exactly, as equality of their defining ideal sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def Closed.Families.FlatClosedFamily.coefficientPullback {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) (φ : CommRingCat.of R ⟶ CommRingCat.of A) :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace A n) :=
  F.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ)
    (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)

theorem Closed.Families.FlatClosedFamily.coefficientPullback_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n))
    (φ : CommRingCat.of R ⟶ CommRingCat.of A) (ψ : CommRingCat.of A ⟶ CommRingCat.of B) :
    (F.coefficientPullback φ).coefficientPullback ψ = F.coefficientPullback (φ ≫ ψ) := by
  apply Closed.Families.FlatClosedFamily.ext
  change (F.ideal.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)).comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap ψ n) =
    F.ideal.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap (φ ≫ ψ) n)
  exact (F.ideal.comap_comp _ _).symm.trans
    (congrArg (fun f => F.ideal.comap f) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_comp φ ψ n).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
