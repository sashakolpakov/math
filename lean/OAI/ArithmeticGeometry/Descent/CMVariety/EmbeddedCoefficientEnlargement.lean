import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters

/-! # Embedded Coefficient Enlargement -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedCoefficientEnlargement.Abelian

noncomputable section

/-! Enlarge a finite coefficient set while retaining the actual projective
embedding and the same ambient-field fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {X : Over (Spec (.of K))} {n : ℕ}

theorem coefficient_enlarge_smooth (M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K X) [Smooth M.model.hom]
    (t : Finset K) (h : M.coefficients ⊆ t) : Smooth (M.enlarge t h).model.hom :=
  inferInstanceAs (Smooth (pullback.snd M.model.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))

theorem coefficient_enlarge_proper (M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K X) [IsProper M.model.hom]
    (t : Finset K) (h : M.coefficients ⊆ t) : IsProper (M.enlarge t h).model.hom :=
  inferInstanceAs (IsProper (pullback.snd M.model.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))

theorem coefficient_enlarge_connected (M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K X)
    [GeometricallyConnected M.model.hom] (t : Finset K) (h : M.coefficients ⊆ t) :
    GeometricallyConnected (M.enlarge t h).model.hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd M.model.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))

theorem coefficient_enlarge_irreducible (M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K X)
    [GeometricallyIrreducible M.model.hom] (t : Finset K) (h : M.coefficients ⊆ t) :
    GeometricallyIrreducible (M.enlarge t h).model.hom :=
  inferInstanceAs (GeometricallyIrreducible (pullback.snd M.model.hom (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)))

def enlargeEmbeddedCoefficientModel (D : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n)
    (t : Finset K) (h : D.toModel.coefficients ⊆ t) : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n := by
  let F := Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let φ := ((Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE h)).hom
  let eP : F.obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K D.toModel.coefficients) n) ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t) n :=
    (AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsIso eP.hom.left := ((Over.forget (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso eP).isIso_hom
  have : IsClosedImmersion (F.map D.embedding).left := MorphismProperty.of_isPullback
    (Models.FoundationsPullback.Constructions.pullback_over_map_isPullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) D.embedding).flip D.closedImmersion
  exact {
    toModel := D.toModel.enlarge t h
    embedding := F.map D.embedding ≫ eP.hom
    closedImmersion := inferInstanceAs (IsClosedImmersion ((F.map D.embedding).left ≫ eP.hom.left)) }

end

end OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedCoefficientEnlargement.Abelian
